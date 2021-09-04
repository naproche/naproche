{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ApplicativeDo #-}

-- | Transform the blocks from a parsed text to TFF form.
-- This code is a bit fragile since it was written mainly
-- by checking that a ton of examples work and not focussing
-- on correctness by design. It should become obsolete
-- as soon as we have a new parser.

module SAD.Core.Transform
 ( transform, transformBlock
 ) where

import Data.Bifunctor
import Data.Text (Text)
import Data.Char (toUpper)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Control.Monad.State
import Data.Foldable (foldrM)
import Data.Function (on)
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Maybe
import Control.Monad.Validate
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import SAD.Data.Formula (Formula, Tag(..), Decl(..), showFormula)
import qualified SAD.Data.Formula as F
import SAD.Data.VarName
import SAD.Data.Terms
import SAD.Data.Text.Block (ProofText(..), Block(..), position)
import qualified SAD.Data.Text.Block as Block
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import SAD.Data.SourcePos (noSourcePos)

import SAD.Data.Identifier
import SAD.Core.AST
import SAD.Core.Errors
import SAD.Core.Unique

newtype Transform m a = Transform
  { fromTransform :: ValidateT (Seq TransformError) (StateT Context m) a
  } deriving (Functor, Applicative, Monad, MonadValidate (Seq TransformError), MonadState Context)

instance MonadTrans Transform where
  lift ma = Transform (lift (lift ma))

instance HasUnique m => HasUnique (Transform m) where
  newIdent n = Transform (lift (lift (newIdent n)))

failWithMessage :: Monad m => TransformErrorMessage -> Transform m a
failWithMessage msg = do
  loc <- currentLocation <$> get
  refute $ Seq.singleton $ TransformError loc msg

errorWithMessage :: Monad m => Doc ann -> Transform m a
errorWithMessage txt = do
  loc <- currentLocation <$> get
  error $ renderString $ layoutSmart
        (defaultLayoutOptions { layoutPageWidth = AvailablePerLine 120 1.0 })
    $  (case errorBlock loc of Nothing -> ""; Just f -> "\nWhile checking the block:\n\n" <> pretty (show f))
    <> (case errorFormula loc of Nothing -> ""; Just f -> "\nmore specifically, the formula:\n\n" <> pretty (showFormula f))
    <> "\n\nInternal: " <> txt
    <> "\n  Please report this in the bugtracker of https://github.com/naproche/naproche\n"

-- | This should be kept in sync with SAD.ForTheL.Base.initFS
-- Equalities can be omitted since they are a feature of TPTP syntax.
predefinedStmts :: HasUnique m => Transform m [Located Stmt]
predefinedStmts = do
  x <- newIdent (NormalIdent "x")
  c <- newIdent (NormalIdent "c")
  let predef = [ Located noSourcePos $ IntroSort identClass
        , Located noSourcePos $ IntroSort identObject
        , Located noSourcePos $ IntroSort identSet
        , Located noSourcePos $ IntroAtom identElement
            [(x, Set.singleton (Signature identObject)), (c, Set.singleton (Signature identClass))] []
        ]
  setClass <- map (Located noSourcePos) <$> mkCoercion (Signature identSet) (Signature identClass)
  setObject <- map (Located noSourcePos) <$> mkCoercion (Signature identSet) (Signature identObject)
  pure $ predef ++ setClass ++ setObject

data Context = Context
  { currentLocation :: TransformErrorLocation
  , sorts :: Map Identifier Ident
    -- ^ the set of known types. We map their source-name to the unique ident, so
    -- we can turn an applied notion into a type declaration.
  , preBoundVars :: Map Ident (Set InType)
    -- ^ a set of names that were registered, so that we can find out which variables
    -- are unbound in a block. We also store the possible types of these names to
    -- derive coercions, but that is hacky and should be removed once we have better
    -- parser support.
  , freeVariables :: Map Identifier Ident
    -- ^ rename all free variables in a block to unique identifiers.
  } deriving (Eq, Ord, Show)

instance Semigroup Context where
  (<>) (Context _ s1 v1 f1) (Context l2 s2 v2 f2) = Context l2 (s1 <> s2) (v1 <> v2) (f1 <> f2)

instance Monoid Context where
  mempty = Context noLocation mempty mempty mempty

-- | Parse a formula into a term while ignoring all type information.
-- This will only checkthat all de-bruijn indices have a binder.
-- We will subsequently use the variable names at
-- the binders instead of indices since this leads to nicer output.
parseFormula :: HasUnique m => Formula -> Transform m Term
parseFormula f = modify (\s -> s { currentLocation = (currentLocation s) { errorFormula = Just f }}) >> go [] f
  where
    go vars = \case
      F.All (Decl v _ _) f -> do
        v' <- checkVar v
        Forall v' mempty <$> go (addVar v' vars) f
      F.Exi (Decl v _ _) f -> do
        v' <- checkVar v
        Exists v' mempty <$> go (addVar v' vars) f
      F.Class (Decl v _ _) f -> do
        v' <- checkVar v
        Class v' mempty Nothing Nothing <$> go (addVar v' vars) f
      F.FinClass fs -> do
        fs' <- mapM (go vars) fs
        pure $ FinClass mempty Nothing fs'
      F.InClass (Decl v _ _) m f -> do
        v' <- checkVar v
        m' <- go vars m
        Class v' mempty (Just m') Nothing <$> go (addVar v' vars) f
      F.Iff f1 f2 -> App Iff <$> mapM (go vars) [f1, f2]
      F.Imp f1 f2 -> App Imp <$> mapM (go vars) [f1, f2]
      F.And f1 f2 -> App And <$> mapM (go vars) [f1, f2]
      F.Or  f1 f2 -> App Or  <$> mapM (go vars) [f1, f2]
      F.Tag HeadTerm (F.Trm (TermNotion sort) [arg] _ _) -> do
        name' <- checkTerm $ TermNotion sort
        arg' <- go vars arg
        pure $ Tag SortTerm $ AppWf (Unresolved name') [arg'] NoWf
      F.Tag t  f  -> Tag t <$> go vars f
      F.Not f -> App Not <$> mapM (go vars) [f]
      F.Top -> pure $ App Top []
      F.Bot -> pure $ App Bot []
      F.Trm TermEquality [f1, f2] _ _ -> App Eq <$> mapM (go vars) [f1, f2]
      F.Trm name args _ _ -> do
        name' <- checkTerm name
        args' <- mapM (go vars) args
        pure $ AppWf (Unresolved name') args' NoWf
      F.Var v _ _ -> do
        fv <- freeVariables <$> get
        case varToIdent v of
          Just vi -> do
            case Map.lookup vi fv of
              Just v' -> pure $ AppWf (Resolved v') [] NoWf
              Nothing -> do
                v' <- newIdent vi
                modify $ \s -> s { freeVariables = Map.insert vi v' (freeVariables s) }
                pure $ AppWf (Resolved v') [] NoWf
          Nothing -> errorWithMessage $ "Parser variable escaped to type-checking: " <> pretty (show v)
      F.Ind i _ ->
        if length vars > i then pure $ AppWf (Resolved $ vars !! i) [] NoWf
        else errorWithMessage $ "Unbound index: " <> pretty i
      f -> errorWithMessage $ pretty $ "Intermittent parse result in type-check: " ++ showFormula f

    addVar v vars = v:vars
    checkVar v = case varToIdent v of
      Just i -> do
        i' <- newIdent i
        modify $ \s -> s { freeVariables = Map.insert i i' (freeVariables s) }
        pure i'
      Nothing -> errorWithMessage $ "Parser variable escaped to type-checking: " <> pretty (show v)
    checkTerm t = case termToIdent t of
      Just i -> pure i
      Nothing -> errorWithMessage $ "Parser term escaped to type-checking: " <> pretty (show t)

-- | Given a list of defined sorts and a TermName,
-- decide if this is a sort.
parseType :: Context -> Identifier -> Maybe InType
parseType ctx t = case Map.lookup t (sorts ctx) of
  Just t' -> Just $ Signature t'
  Nothing -> Nothing

-- | Transform type predicates into types.
extractGivenTypes :: Monad m => Context -> Term -> Transform m Term
extractGivenTypes ctx t = fmap fst $ runWriterT $ runReaderT (go t) mempty
  where
    go :: Monad m => Term -> ReaderT (Set Ident, Set Ident) (WriterT (Map Ident (Set InType)) (Transform m)) Term
    go = \case
      Forall v _ t -> do
        (t', typings) <- listen $ local (first (Set.insert v)) $ go t
        let m = Map.findWithDefault mempty v typings
        pure $ Forall v m t'
      Exists v _ t -> do
        (t', typings) <- listen $ local (second (Set.insert v)) $ go t
        let m = Map.findWithDefault mempty v typings
        pure $ Exists v m t'
      Class v _ Nothing _ t -> do
        (t', typings) <- listen $ local (second (Set.insert v)) $ go t
        let m = Map.findWithDefault mempty v typings
        pure $ Class v m Nothing Nothing t'
      Class v _ (Just m) _ t -> do
        (t', typings) <- listen $ local (second (Set.insert v)) $ go t
        let typ = Map.findWithDefault mempty v typings
        m' <- go m
        pure $ Class v typ (Just m') Nothing t'
      FinClass _ _ ts -> do
        ts' <- mapM go ts
        pure $ FinClass mempty Nothing ts'
      AppWf (Unresolved op') args _ -> do
        settable <- snd <$> ask
        case parseType ctx op' of
          Just t -> case args of
            [AppWf (Resolved v) [] _] | v `Set.member` settable -> do
              tell $ Map.singleton v (Set.singleton t)
              pure $ App Top []
            [arg] -> do
              arg' <- local (const mempty) $ go arg
              pure $ Typing t arg'
            [] -> lift $ lift $ errorWithMessage "Sort applied to no arguments!"
            _ -> lift $ lift $ errorWithMessage "Sort applied to several arguments!"
          Nothing -> do
            args' <- mapM (local (const mempty) . go) args
            pure $ AppWf (Unresolved op') args' NoWf
      AppWf (Resolved v) args _ -> do
        args' <- mapM (local (const mempty) . go) args
        pure $ AppWf (Resolved v) args' NoWf
      App Imp [a, b] -> do
        a' <- local (\(a, b) -> (mempty, a <> b)) $ go a
        b' <- go b
        pure $ App Imp [a', b']
      App And [a, b] -> do
        a' <- go a
        b' <- go b
        pure $ App And [a', b']
      App Iff [Tag tag a, b] -> do -- for predicate definitions
        a' <- go a
        b' <- local (\(a, b) -> (mempty, a <> b)) $ go b
        pure $ App Iff [Tag tag a', b']
      App op args -> do
        args' <- mapM (local (const mempty) . go) args
        pure $ App op args'
      Coe cs t -> Coe cs <$> go t
      Typing ty t -> Typing ty <$> go t
      Tag tag t -> Tag tag <$> go t

coercionName :: HasUnique m => Ident -> Ident -> Transform m (Ident, Ident)
coercionName i1 i2 = do
  (n1, n2) <- case (sourceIdentifier i1, sourceIdentifier i2) of
    (NormalIdent n1, NormalIdent n2) -> pure (n1, n2)
    _ -> failWithMessage CoercionsBetweenNonNotions
  let name' = n2 <> "From" <> beginUpper n1
  name <- newIdent $ NormalIdent name'
  nameInj <- newIdent $ NormalIdent $ name' <> "Inj"
  pure (name, nameInj)
  where
    beginUpper t = case Text.uncons t of
      Just (c, t') -> Text.cons (toUpper c) t'
      Nothing -> t

mkCoercion :: HasUnique m => InType -> InType -> Transform m [Stmt]
mkCoercion (Signature from) (Signature to) = do
  (name, nameInj) <- coercionName from to
  vars <- mapM (newIdent . NormalIdent) ["x", "y"]
  let [x, y] = vars
      coe = \x -> AppWf (Resolved name) [x] NoWf
      fromType = Set.singleton $ Signature from
      inj = NFTerm [(x, fromType), (y, fromType)]
        [App Eq [coe (AppWf (Resolved x) [] NoWf), coe (AppWf (Resolved y) [] NoWf)]]
        (App Eq [AppWf (Resolved x) [] NoWf, AppWf (Resolved y) [] NoWf])
  pure [Coercion name from to, Axiom nameInj inj]

-- | Make sure that there are no tags left.
noTags :: Monad m => Term -> Transform m Term
noTags expr = go expr
  where
    go = \case
      Forall v m t -> Forall v m <$> go t
      Exists v m t -> Exists v m <$> go t
      Class v m Nothing ci t -> Class v m Nothing ci <$> go t
      Class v m (Just mm) ci t -> do
        mm' <- go mm
        Class v m (Just mm') ci <$> go t
      FinClass m cv ts -> FinClass m cv <$> mapM go ts
      AppWf op args _ -> flip (AppWf op) NoWf <$> mapM go args
      App op args -> App op <$> mapM go args
      Coe cs t -> Coe cs <$> go t
      Typing ty t -> Typing ty <$> go t
      Tag Replacement t -> go t
      Tag EqualityChain t -> go t
      Tag tag _ -> errorWithMessage $ "Remaining tag: " <> pretty (show tag) <> line
        <> "in expression: " <> pretty expr

bindAllExceptKnown :: Context -> Term -> Term
bindAllExceptKnown ctx = bindAllExcept (Map.keysSet $ preBoundVars ctx)

transformFormula :: HasUnique m => Formula -> Transform m Term
transformFormula f = do
  t <- parseFormula f
  ctx <- get
  t' <- extractGivenTypes ctx $ bindAllExceptKnown ctx t
  noTags t'

-- | A tactic takes the current context and a number of proof lines (Block)
-- and may translate some lines and give a new goal.
type Tactic m = [Block] -> Transform m (Maybe (Located Prf, [Block]))

preBind :: Monad m => Map Ident (Set InType) -> Transform m ()
preBind vs = do
  modify $ \ctx -> ctx { preBoundVars = vs <> preBoundVars ctx }

-- | Convert a single line of a proof.
subClaim :: HasUnique m => Block -> Transform m (Located Prf)
subClaim bl@(Block f b _ _ n l _) = Located (position bl) <$> do
  mainF@(NFTerm ex _ _) <- checkNF . termToNF =<< transformFormula f
  name <- newIdent $ NormalIdent n
  preBind (Map.fromList ex)
  Subclaim name mainF <$> convertProof l b

subClaims :: HasUnique m => Tactic m
subClaims [] = pure Nothing
subClaims (b:bs) = do
  sc <- subClaim b
  pure $ Just (sc, bs)

byContradiction :: Monad m => Tactic m
byContradiction [] = pure Nothing
byContradiction (b:bs) = pure $ case formula b of
  F.Not (F.Trm TermThesis [] _ _) ->
    Just (Located (position b) (ByContradiction (App Top [])), bs)
  _ -> Nothing

splitExists :: Set Ident -> Term -> (Map Ident (Set InType), Term)
splitExists vs t = let (a, b) = go t in (Map.fromList a, b)
  where
    go = \case
      Exists v m t | v `Set.member` vs ->
        let (hs, t') = go t
        in ((v, m):hs, t')
      Exists v m t ->
        let (hs, t') = go t
        in (hs, Exists v m t')
      t -> ([], t)

define :: HasUnique m => Tactic m
define [] = pure $ Nothing
define (b:bs) = case (formula b, Set.toList $ declaredVariables b) of
  (F.Trm { F.trmName = TermEquality, F.trmArgs = [F.Var v0 [] _, def]}, [Decl v1 _ _]) | v0 == v1 -> do
    let l = position b
        varToIdent' v = case varToIdent v of
          Just a -> a
          Nothing -> error $ "Parser variable in define tactic!"
        v1 = varToIdent' v0
    x <- newIdent v1 
    preBind (Map.singleton x mempty)
    modify $ \s -> s { freeVariables = Map.insert v1 x (freeVariables s) }
    f <- transformFormula def
    pure $ Just $ (Located l $ Define x mempty f, bs)
  _ -> pure $ Nothing

chooses :: HasUnique m => Tactic m
chooses [] = pure $ Nothing
chooses (b:bs) = case kind b of
  Block.Selection -> do
    let l = position b
        varToIdent' v = case varToIdent v of
          Just a -> a
          Nothing -> error "Parser variable in chooses tactic!"
        vs' = Set.toList $ Set.map (varToIdent' . declName) $ declaredVariables b
    vs'' <- mapM (\v -> newIdent v >>= \vi -> pure (v, vi)) vs'
    let vs = Set.fromList $ map snd vs''
        bindExists vs tr = foldr (\v -> Exists v mempty) tr vs
    ctx <- get
    modify $ \s -> s { freeVariables = foldr (uncurry Map.insert) (freeVariables s) vs'' }
    f <- parseFormula (formula b)
      >>= extractGivenTypes ctx . bindAllExceptKnown ctx . bindExists (Set.toList vs)
      >>= noTags
    let (boundVs, fHypo) = splitExists vs f
    preBind boundVs
    p <- convertProof (link b) (body b)
    pure $ Just (Located l $ Choose (Map.toList boundVs) fHypo p, bs)
  _ -> pure Nothing

cases :: HasUnique m => Tactic m
cases bs = go Nothing bs
  where
    parseCase c b = do
      c' <- transformFormula c
      p' <- convertProof (link b) (body b)
      let l' = position b
      pure (l', (c', p'))

    go Nothing [] = pure Nothing
    go (Just (l, ms)) [] = pure $ Just (Located l $ TerminalCases (reverse ms), [])
    go m (b:bs) = case formula b of
      F.Imp (F.Tag CaseHypothesisTag c) (F.Trm TermThesis [] _ _) -> do
        (l', (c', p')) <- parseCase c b
        case m of
          Nothing -> go (Just (l', [(c', p')])) bs
          Just (l, ms) -> go (Just (l, (c', p'):ms)) bs
      _ -> pure $ case m of
        Nothing -> Nothing
        Just (l, ms) -> Just (Located l $ Cases (reverse $ map (\(a, b) -> (a, App Top [], b)) ms), (b:bs))

-- | Convert a Proof. ... end. part
convertProof :: HasUnique m => [Text] -> [ProofText] -> Transform m PrfBlock
convertProof links pts = do
  (_, ps) <- go $ concatMap (\case ProofTextBlock b -> [b]; _ -> []) pts
  case ps of
    [] -> pure $ ProofByHints links
    _ -> pure $ ProofByTactics ps
  where
    go bs = unfoldM bs $ \st ->
      takeFirstSucceding
        [ byContradiction st
        , cases st
        , chooses st
        , define st
        , subClaims st
        ]

    takeFirstSucceding :: Monad m => [m (Maybe a)] -> m (Maybe a)
    takeFirstSucceding [] = pure Nothing
    takeFirstSucceding (x:xs) = do
      m <- x
      case m of
        Just a -> pure $ Just a
        Nothing -> takeFirstSucceding xs

    unfoldM :: Monad m => b -> (b -> Transform m (Maybe (a, b))) -> Transform m (b, [a])
    unfoldM b f = do
      fb <- f b
      case fb of
        Just (a, b') -> fmap (a:) <$> unfoldM b' f
        Nothing -> pure (b, [])

-- | Get the blocks in a Prooftext.
getBlocks :: Monad m => ProofText -> Transform m [Block]
getBlocks (ProofTextBlock b) = pure [b]
getBlocks (ProofTextRoot ts) = concat <$> mapM getBlocks ts
getBlocks p = errorWithMessage $ pretty $ "getBlocks received: " ++ show p

checkNF :: Monad m => NFTerm -> Transform m NFTerm
checkNF nf@(NFTerm im _ _) = case findDuplicate Map.empty im of
  Just (x, y) -> failWithMessage $ DuplicateForallBind x y
  Nothing -> pure nf
  where
    findDuplicate m [] = Nothing
    findDuplicate m (x:xs) = case Map.lookup (fst x) m of
      Just y -> Just (x, (fst x, y))
      Nothing -> findDuplicate (Map.insert (fst x) (snd x) m) xs

-- | Given a term and a list of typings, make sure the term is a variable
-- and return its set of types. If it is not typed or the set of types is empty,
-- throw an error.
extractExplicit :: Monad m => Identifier -> [(Ident, Set InType)] -> [Term] -> Transform m [(Ident, Set InType)]
extractExplicit name implicit args = removeMap =<< foldrM (flip go) (Map.fromList implicit, []) args
  where
    removeMap (m, a) = case Map.toList m of
      [] -> pure a
      m -> errorWithMessage $ "The following variables are unbound: " <> pretty (show m)

    -- Variables are always resolved
    go (im, ex) (AppWf (Resolved v) [] _) = case Map.lookup v im of
      Just s -> pure (Map.delete v im, (v, s):ex)
      Nothing -> failWithMessage $ FunDefUnboundVariable name v
    go _ e = failWithMessage $ FunDefTermNotVariable name e

-- | Extract definitions from a typed term.
-- This will find HeadTerms and add them as definitions,
-- as well as delete all HeadTerm Tags.
extractDefinitions :: HasUnique m => Context -> NFTerm -> Transform m [Stmt]
extractDefinitions ctx nf = do
  (asDefs, nf) <- case reverse $ nfAssumptions nf of
        -- sorts definitions
        (Tag SortTerm (AppWf (Unresolved name) [AppWf (Resolved v) [] _] _)):assms -> do
          name' <- case parseType ctx name of
            Just _ -> failWithMessage $ OverloadedNotion name
            Nothing -> newIdent name
          case nfBody nf of
            Typing to (AppWf (Resolved v1) [] _) | v == v1 -> do
              coe <- mkCoercion (Signature name') to
              pure (IntroSort name' : coe, NFTerm [] [] (App Top []))
            -- e.g. a region is an open set -> cond is open(h5):
            App And [Typing to (AppWf (Resolved v1) [] _), cond] | v == v1 -> do
              coe <- mkCoercion (Signature name') to
              ex <- extractExplicit name (nfArguments nf) [AppWf (Resolved v) [] NoWf]
              as <- mapM noTags $ reverse assms
              cond' <- noTags cond
              condName <- newIdent name
              pure ([IntroSort name', Axiom condName (NFTerm ex as cond')] ++ coe, NFTerm [] [] (App Top []))
            App Top [] -> pure ([IntroSort name'], NFTerm [] [] (App Top []))
            _ -> failWithMessage $ MalformedTypeDecl nf
        -- Atoms and signatures.
        (Tag HeadTerm (AppWf (Unresolved name) args _)):assms -> do
          ex <- extractExplicit name (nfArguments nf) args
          as <- mapM noTags $ reverse assms
          name' <- newIdent name
          pure ([IntroAtom name' ex as], NFTerm [] [] (App Top []))
        (Tag HeadTerm (App Eq [AppWf (Resolved v0) [] _, AppWf (Unresolved name) args _])):assms -> do
          as <- mapM noTags $ reverse assms
          ex <- extractExplicit name (nfArguments nf) (args ++ [AppWf (Resolved v0) [] NoWf])
          let ex' = List.deleteBy ((==) `on` fst) (v0, mempty) ex
          name' <- newIdent name
          axName <- newIdent name
          case nfBody nf of
            Typing to (AppWf (Resolved v1) [] _) | v0 == v1 -> do
              pure ([IntroSignature name' (Set.singleton to) ex' as], NFTerm [] [] (App Top []))
            -- e.g. 1 is a nonzero natural number -> cond is 1 != 0:
            App And [Typing to (AppWf (Resolved v1) [] _), cond] | v0 == v1 -> do
              cond' <- noTags cond
              pure ([IntroSignature name' (Set.singleton to) ex' as
                    , Axiom axName (NFTerm ex' as (subst v1 (AppWf (Unresolved name) (map (\(i, _) -> AppWf (Resolved i) [] NoWf) ex) NoWf) cond'))
                    ], NFTerm [] [] (App Top []))
            _ -> failWithMessage $ MalformedSignatureDecl nf
        _ -> pure ([], nf)
  bdDefs <- case nfBody nf of
        -- TODO: This case does not match when the coercion already exists and thus an error
        -- 'Remaining tag: CoercionTag' is thrown!
        Tag CoercionTag (Typing to (AppWf (Resolved v0) [] _)) ->
          case List.lookup v0 (nfArguments nf) of
            (Just from) -> do
              case Set.toList from of
                [] -> failWithMessage CoercionFromNotProvided
                xs@(_:_:_) -> failWithMessage $ CoercionFromNotUnique xs
                [from] -> mkCoercion from to
            _ -> errorWithMessage "Couldn't parse coercion!"
        -- predicate definitions
        App Iff [Tag tag (AppWf (Unresolved name) args _), def]
          | tag == HeadTerm || tag == SortTerm -> do
          as <- mapM noTags $ nfAssumptions nf
          b <- noTags $ def
          ex <- extractExplicit name (nfArguments nf) args
          name' <- newIdent name
          pure [Predicate name' $ NFTerm ex as b]
        Forall v0 m (App Iff [Tag HeadTerm (AppWf (Unresolved name) ((AppWf (Resolved v1) [] _):args) _), def]) | v0 == v1 -> do
          as <- mapM noTags $ nfAssumptions nf
          b <- noTags $ def
          ex <- extractExplicit name (nfArguments nf) args
          name' <- newIdent name
          pure [Predicate name' $ NFTerm ((v0, m):ex) as b]
        -- function definitions
        Forall _ retval (App Iff [Tag HeadTerm (App Eq [AppWf v0 [] _, AppWf (Unresolved name) args _]), App Eq [AppWf v1 [] _, def]]) | v0 == v1 -> do
          as <- mapM noTags $ nfAssumptions nf
          b <- noTags def
          ex <- extractExplicit name (nfArguments nf) args
          name' <- newIdent name
          pure [Function name' retval $ NFTerm ex as b]
        App Iff [Tag HeadTerm (App Eq [AppWf (Resolved v0) _ _, AppWf (Unresolved name) args _]), App Eq [_, def]]
          | isJust (List.lookup v0 (nfArguments nf)) -> do
          as <- mapM noTags $ nfAssumptions nf
          b <- noTags $ def
          ex <- extractExplicit name (nfArguments nf) (args ++ [AppWf (Resolved v0) [] NoWf])
          let ex' = List.deleteBy ((==) `on` fst) (v0, mempty) ex
          let retval = case List.lookup v0 (nfArguments nf) of Just r -> r; Nothing -> error "Can't happen"
          name' <- newIdent name
          pure [Function name' retval $ NFTerm ex' as b]
        Forall _ retval (App Imp [Tag HeadTerm (App Eq [AppWf (Resolved v0) [] _, AppWf (Unresolved name) args _]), def]) -> do
          as <- mapM noTags $ nfAssumptions nf
          b <- noTags $ def
          ex <- extractExplicit name (nfArguments nf) args
          name' <- newIdent name
          case b of
            Typing to (AppWf (Resolved v1) [] _) | v0 == v1 -> do
              pure [IntroSignature name' (Set.singleton to) ex as]
            _ -> pure [Function name' retval $ NFTerm ex as b]
        _ -> do
          as <- mapM noTags (nfAssumptions nf)
          b <- noTags $ nfBody nf
          axName <- newIdent $ NormalIdent "ax"
          if b /= App Top []
            then pure [Axiom axName (NFTerm (nfArguments nf) as b)]
            else pure []
  pure $ asDefs ++ bdDefs

-- | Convert a block into a statement.
transformBlock :: HasUnique m => Block -> Transform m [Located Stmt]
transformBlock bl@(Block f b _ _ n l _) = map (Located (position bl)) <$>
  case f of
    -- top-level blocks:
    (F.Var (VarHole _) _ _) -> do
      gottenBlocks <- reverse . concat <$> mapM getBlocks b
      case gottenBlocks of
        [] -> errorWithMessage "list of blocks is empty"
        (main:assms) -> do
          let mainF = foldl (flip F.Imp) (formula main) (formula <$> assms)
          ctx <- get
          mainT <- parseFormula mainF >>= extractGivenTypes ctx . bindAllExceptKnown ctx
          let mainT' = termToNF mainT
          if Block.needsProof bl then (do
            nfT <- noTags mainT
            nfT' <- checkNF $ termToNF nfT
            name <- newIdent (NormalIdent n)
            preBind (Map.fromList $ nfArguments nfT')
            (:[]) . Claim name nfT' <$> convertProof l (body main))
            else extractDefinitions ctx mainT'
    _ -> errorWithMessage "transformBlock should not be applied to proofs!"

transform :: HasUnique m => [ProofText] -> m (Either (Seq TransformError) [Located Stmt])
transform = flip evalStateT mempty . runValidateT . fromTransform
  . begin . concatMap (\case ProofTextBlock bl -> [bl]; _ -> [])
  where
    begin xs = do
      stmts <- predefinedStmts
      mapM_ updateCtx stmts
      (stmts ++) <$> go xs

    go :: HasUnique m => [Block] -> Transform m [Located Stmt]
    go [] = pure []
    go (b:bs) = do
      modify $ \s -> s { currentLocation = (currentLocation s) { errorBlock = Just b } }
      modify $ \s -> s { currentLocation = (currentLocation s) { errorPosition = position b } }
      stmts <- transformBlock b
      mapM_ updateCtx stmts
      (stmts ++) <$> go bs

    updateCtx :: Monad m => Located Stmt -> Transform m ()
    updateCtx (Located _ s) = do
      modify $ \s -> s { freeVariables = mempty }
      case s of
        IntroSort n -> modify $ \s -> s { sorts = Map.insert (sourceIdentifier n) n (sorts s) }
        _ -> pure ()
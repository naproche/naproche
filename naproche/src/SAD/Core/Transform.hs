{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

-- | Transform the blocks from a parsed text to TFF form.
-- This code is a bit fragile since it was written mainly
-- by checking that a ton of examples work and not focussing
-- on correctness by design. It should become obsolete
-- as soon as we have a new parser.

module SAD.Core.Transform
 ( transform, transformBlock
 ) where

import Data.Text (Text)
import Data.Char (toUpper)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Functor.Const
import qualified Data.List as List
import Control.Monad.State
import Data.Foldable (foldrM)
import Data.Function (on)
import Control.Monad.Reader
import Control.Monad.Writer

import SAD.Data.Formula (Formula, Tag(..), Decl(..), showFormula)
import qualified SAD.Data.Formula as F
import SAD.Data.VarName
import SAD.Data.Terms
import SAD.Data.Text.Block (ProofText(..), Block(..), position)
import qualified SAD.Data.Text.Block as Block
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import SAD.Core.SourcePos (SourcePos, noSourcePos)
import qualified SAD.Core.Message as Message
import qualified Isabelle.Naproche as Naproche

import SAD.Data.Identifier
import SAD.Core.Typed

data ErrorContext = ErrorContext
  { errorBlock :: Block
  , errorFormula :: Formula
  , errorPosition :: SourcePos
  } deriving (Eq, Ord, Show)

type Err m a = StateT ErrorContext m a

failWithMessage :: Message.Comm m => Doc ann -> Err m a
failWithMessage txt = do
  src <- errorPosition <$> get
  f <- errorFormula <$> get
  b <- errorBlock <$> get
  w <- lift $ Message.textFieldWidth
  lift $ Message.error Naproche.origin_reasoner src
    $  "\nWhile checking the block:\n\n" ++ show b
    ++ "\nmore specifically, the formula:\n\n" ++ showFormula f
    ++ "\n\n" ++ (renderString $ layoutSmart
      (defaultLayoutOptions { layoutPageWidth = AvailablePerLine w 1.0 }) txt)

data Context = Context
  { sorts :: Set Ident
  , preBoundVars :: Map Ident (Set InType)
  } deriving (Eq, Ord, Show)

instance Semigroup Context where
  (<>) (Context s1 v1) (Context s2 v2) = Context (s1 <> s2) (v1 <> v2)

-- | This should be kept in sync with SAD.ForTheL.Base.initFS
-- Equalities can be omitted since they are a feature of TPTP syntax.
instance Monoid Context where
  mempty = Context (Set.fromList [identClass, identObject]) (Map.singleton identElement mempty)

-- | Parse a formula into a term while ignoring all type information.
-- This will only checkthat all de-bruijn indices have a binder.
-- We will subsequently use the variable names at
-- the binders instead of indices since this leads to nicer output.
parseFormula :: Message.Comm m => Formula -> Err m (Term (Const ()) Tag)
parseFormula f = modify (\s -> s { errorFormula = f }) >> go [] f
  where 
    go vars = \case
      F.All (Decl v _ _) f -> do
        v' <- checkVar v
        Forall v' (Const ()) <$> go (addVar v' vars) f
      F.Exi (Decl v _ _) f -> do
        v' <- checkVar v
        Exists v' (Const ()) <$> go (addVar v' vars) f
      F.Class (Decl v _ _) f -> do
        v' <- checkVar v
        Class v' (Const ()) <$> go (addVar v' vars) f
      F.Iff f1 f2 -> App Iff <$> mapM (go vars) [f1, f2]
      F.Imp f1 f2 -> App Imp <$> mapM (go vars) [f1, f2]
      F.And f1 f2 -> App And <$> mapM (go vars) [f1, f2]
      F.Or  f1 f2 -> App Or  <$> mapM (go vars) [f1, f2]
      F.Tag HeadTerm (F.Trm (TermNotion sort) [arg] _ _) -> do
        name' <- checkTerm $ TermNotion sort
        arg' <- go vars arg
        pure $ Tag SortTerm $ AppWf name' [arg'] noWf
      F.Tag t  f  -> Tag t <$> go vars f
      F.Not f -> App Not <$> mapM (go vars) [f]
      F.Top -> pure $ App Top []
      F.Bot -> pure $ App Bot []
      F.Trm TermEquality [f1, f2] _ _ -> App Eq <$> mapM (go vars) [f1, f2]
      F.Trm name args _ _ -> do
        name' <- checkTerm name
        args' <- mapM (go vars) args
        pure $ AppWf name' args' noWf
      F.Var v _ _ -> do
        v' <- checkVar v
        pure $ AppWf v' [] noWf
      F.Ind i _ ->
        if length vars > i then pure $ AppWf (vars !! i) [] noWf
        else failWithMessage $ pretty $ "Internal error: Unbound index: " ++ show i
      f -> failWithMessage $ pretty
        $ "Internal error: Intermittent parse result in type-check: " ++ show f

    addVar v vars = v:vars
    checkVar v = case varToIdent v of
      Just i -> pure i
      Nothing -> failWithMessage $ pretty
        $ "Internal error: Internal parser variable escaped to type-checking: " ++ show v
    checkTerm t = case termToIdent t of
      Just i -> pure i
      Nothing -> failWithMessage $ pretty
        $ "Internal error: Internal parser term escaped to type-checking: " ++ show t

-- | Given a list of defined sorts and a TermName,
-- decide if this is a sort.
parseType :: Context -> Ident -> Maybe InType
parseType ctx t = case Set.member t (sorts ctx) of
  True -> Just $ Signature t
  False -> Nothing

-- | Transform type predicates into types.
extractGivenTypes :: Message.Comm m => Context -> Term (Const ()) Tag -> Err m (Term Set Tag)
extractGivenTypes ctx t = fmap (fst) $ runWriterT $ runReaderT (go t) mempty
  where
    go :: Message.Comm m => Term (Const ()) Tag -> ReaderT ((Set Ident, Set Ident)) (WriterT (Map Ident (Set InType)) (StateT ErrorContext m)) (Term Set Tag)
    go = \case
      Forall v (Const ()) t -> do
        (t', typings) <- listen $ local (\(a, b) -> (Set.insert v a, b)) $ go t
        let m = Map.findWithDefault mempty v typings
        pure $ Forall v m t'
      Exists v (Const ()) t -> do
        (t', typings) <- listen $ local (\(a, b) -> (a, Set.insert v b)) $ go t
        let m = Map.findWithDefault mempty v typings
        pure $ Exists v m t'
      Class v (Const ()) t -> do
        (t', typings) <- listen $ go t
        let m = Map.findWithDefault mempty v typings
        pure $ Class v m t'
      AppWf op args _ -> do
        settable <- snd <$> ask
        case parseType ctx op of
          Just t -> case args of
            [AppWf v [] _] | v `Set.member` settable -> do
              tell $ Map.singleton v (Set.singleton t)
              pure $ App Top []
            [arg] -> do
              let d = newIdent (NormalIdent "d") (SAD.Data.Identifier.fvToVarSet $ findFree arg)
              arg' <- local (const mempty) $ go arg
              pure $ Exists d (Set.singleton t) $ App Eq [AppWf d [] noWf, arg']
            [] -> lift $ lift $ failWithMessage $ "Internal: Sort applied to no arguments!"
            _ -> lift $ lift $ failWithMessage $ "Internal: Sort applied to several arguments!"
          Nothing -> do
            args' <- mapM (local (const mempty) . go) args
            pure $ AppWf op args' noWf
      -- this hack allows for new coercions in a lemma or axiom
      -- if it is of the form "Let s be a from. Then s is a to."
      App Imp [AppWf (parseType ctx -> Just from) [AppWf v0 [] _] _, AppWf name@(parseType ctx -> Just _) [AppWf v1 [] _] _]
        | v0 == v1 -> do
          tell $ Map.singleton v0 (Set.singleton from)
          pure $ Tag CoercionTag $ AppWf name [AppWf v0 [] noWf] noWf
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
      Tag tag t -> (Tag tag) <$> go t

coercionName :: Message.Comm m => Ident -> Ident -> Err m Ident
coercionName (NormalIdent n1) (NormalIdent n2) = pure $ NormalIdent $ n2 <> "From" <> beginUpper n1
  where beginUpper t = case Text.uncons t of
          Just (c, t') -> Text.cons (toUpper c) t'
          Nothing -> t
coercionName _ _ = failWithMessage $ "Coercions only between notions"

mkCoercion :: Message.Comm m => InType -> InType -> Err m [Stmt Set ()]
mkCoercion (Signature from) (Signature to) = do
  name <- coercionName from to
  let [x, y] = [NormalIdent "x", NormalIdent "y"]
  let coe = \x -> AppWf name [x] noWf
  let fromType = Set.singleton $ Signature from
  let inj = NFTerm [(x, fromType), (y, fromType)] []
        [App Eq [coe (AppWf x [] noWf), coe (AppWf y [] noWf)]]
        (App Eq [AppWf x [] noWf, AppWf y [] noWf])
  pure [Coercion name from to, Axiom inj]

-- | Make sure that there are no tags left.
noTags :: Message.Comm m => Term f Tag -> Err m (Term f ())
noTags = go
  where
    go = \case
      Forall v m t -> Forall v m <$> go t
      Exists v m t -> Exists v m <$> go t
      Class v m t -> Class v m <$> go t
      AppWf op args _ -> flip (AppWf op) noWf <$> mapM go args
      App op args -> App op <$> mapM go args
      Tag Replacement t -> go t
      Tag EqualityChain t -> go t
      Tag tag _ -> failWithMessage $ pretty $ "Remaining tag: " ++ show tag

transformFormula :: Message.Comm m => Context -> Formula -> Err m (Term Set ())
transformFormula ctx f =
  parseFormula f >>= extractGivenTypes ctx . bindAllExcept (Set.union (sorts ctx) $ Map.keysSet $ preBoundVars ctx) >>= noTags

-- | A tactic takes the current context and a number of proof lines (Block)
-- and may translate some lines and give a new goal.
type Tactic m = (Context, [Block]) -> Err m (Maybe (Located (Prf Set ()), (Context, [Block])))

preBind :: Map Ident (Set InType) -> Context -> Context
preBind vs ctx = ctx { preBoundVars = vs <> preBoundVars ctx }

-- | Convert a single line of a proof.
subClaim :: Message.Comm m => Context -> Block -> Err m (Located (Prf Set ()))
subClaim ctx bl@(Block f b _ _ n l _) = Located n (position bl) <$> do
  mainF@(NFTerm im _ _ _) <- checkNF =<< termToNF <$> transformFormula ctx f
  Subclaim mainF <$> convertProof l (preBind (Map.fromList im) ctx) b

subClaims :: Message.Comm m => Tactic m
subClaims (_, []) = pure Nothing
subClaims (ctx, (b:bs)) = do
  sc <- subClaim ctx b
  pure $ Just (sc, (ctx, bs))

byContradiction :: Message.Comm m => Tactic m
byContradiction (_, []) = pure Nothing
byContradiction (ctx, (b:bs)) = pure $ case formula b of
  F.Not (F.Trm TermThesis [] _ _) ->
    Just (Located (name b) (position b) (ByContradiction (App Top [])), (ctx, bs))
  _ -> Nothing

splitExists :: Set Ident -> Term Set () -> (Map Ident (Set InType), Term Set ())
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

chooses :: Message.Comm m => Tactic m
chooses (_, []) = pure $ Nothing
chooses (ctx, (b:bs)) = case kind b of
  Block.Selection -> do
    let l = position b; n = name b
        varToIdent' v = case varToIdent v of
          Just a -> a
          Nothing -> error $ "Parser variable in chooses tactic!"
        vs = Set.map (varToIdent' . declName) $ declaredVariables b
        bindExists vs tr = foldr (\v -> Exists v (Const ())) tr vs

    f <- parseFormula (formula b) 
      >>= extractGivenTypes ctx . bindAllExcept (Set.union (sorts ctx) $ Map.keysSet $ preBoundVars ctx) . bindExists (Set.toList vs)
      >>= noTags
    let (boundVs, fHypo) = splitExists vs f
        ctx' = preBind boundVs ctx
    p <- convertProof (link b) ctx (body b)
    pure $ Just $ (Located n l $ Choose (Map.toList boundVs) fHypo p, (ctx', bs))
  _ -> pure $ Nothing

cases :: Message.Comm m => Tactic m
cases (ctx, bs) = go Nothing bs
  where
    parseCase c b = do
      c' <- transformFormula ctx c
      p' <- convertProof (link b) ctx (body b)
      let l' = (position b)
      pure (l', (c', p'))

    go Nothing [] = pure $ Nothing
    go (Just (l, ms)) [] = pure $ Just (Located "cases" l $ TerminalCases (reverse ms), (ctx, []))
    go m (b:bs) = case formula b of
      F.Imp (F.Tag CaseHypothesisTag c) (F.Trm TermThesis [] _ _) -> do
        (l', (c', p')) <- parseCase c b
        case m of
          Nothing -> go (Just (l', [(c', p')])) bs
          Just (l, ms) -> go (Just (l, (c', p'):ms)) bs
      _ -> pure $ case m of
        Nothing -> Nothing
        Just (l, ms) -> Just (Located "cases" l $ Cases (reverse $ map (\(a, b) -> (a, App Top [], b)) ms), (ctx, b:bs))

-- | Convert a Proof. ... end. part
convertProof :: Message.Comm m => [Text] -> Context -> [ProofText] -> Err m (PrfBlock Set ())
convertProof links ctx pts = do
  ((_, _), ps) <- go $ concatMap (\case ProofTextBlock b -> [b]; _ -> []) pts
  case ps of
    [] -> pure $ ProofByHints links
    _ -> pure $ ProofByTactics ps
  where
    go bs = unfoldM (ctx, bs) $ \st ->
      takeFirstSucceding
        [ byContradiction st
        , cases st
        , chooses st
        , subClaims st
        ]

    takeFirstSucceding :: Monad m => [m (Maybe a)] -> m (Maybe a)
    takeFirstSucceding [] = pure Nothing
    takeFirstSucceding (x:xs) = do
      m <- x
      case m of
        Just a -> pure $ Just a
        Nothing -> takeFirstSucceding xs

    unfoldM :: Message.Comm m => b -> (b -> Err m (Maybe (a, b))) -> Err m (b, [a])
    unfoldM b f = do
      fb <- f b
      case fb of
        Just (a, b') -> fmap (a:) <$> unfoldM b' f
        Nothing -> pure (b, [])

-- | Get the blocks in a Prooftext.
getBlocks :: Message.Comm m => ProofText -> Err m [Block]
getBlocks (ProofTextBlock b) = pure [b]
getBlocks (ProofTextRoot ts) = concat <$> mapM getBlocks ts
getBlocks p = failWithMessage $ pretty $ "Internal error: getBlocks received: " ++ show p

checkNF :: Message.Comm m => NFTerm Set () -> Err m (NFTerm Set ())
checkNF nf@(NFTerm im [] _ _) = if length (Map.toList $ Map.fromList im) == length im
  then pure nf else failWithMessage $ "NFTerm: Duplicate forall bind!"
checkNF _ = failWithMessage $ "NFTerm has explicit variables!"

-- | Given a term and a list of typings, make sure the term is a variable
-- and return it's set of types. If it is not typed or the set of types is empty,
-- throw an error.
extractExplicit :: Message.Comm m => Ident -> [(Ident, Set p)] -> [Term Set Tag] -> Err m ([(Ident, Set p)], [(Ident, Set p)])
extractExplicit name implicit args = removeMap <$> foldrM (flip go) (Map.delete name $ Map.fromList implicit, []) args
  where 
    removeMap (m, a) = (Map.toList m, a)

    go (im, ex) (AppWf v [] _) = case Map.lookup v im of
      Just s -> pure (Map.delete v im, (v, s):ex)
      Nothing -> failWithMessage $ "In a definition for " <> pretty name
        <> ", the variable " <> pretty v <> " was found to be unbound."
    go _ e = failWithMessage $ "In a definition for " <> pretty name
      <> ", I expected a variable, but got:\n" <> pretty e

-- | Extract definitions from a typed term.
-- This will find HeadTerms and add them as definitions,
-- as well as delete all HeadTerm Tags.
extractDefinitions :: Message.Comm m => Context -> NFTerm Set Tag -> Err m [Stmt Set ()]
extractDefinitions ctx nf = do
  (asDefs, nf) <- case reverse $ nfAssumptions nf of
        -- sorts definitions
        (Tag SortTerm (AppWf name [AppWf v [] _] _)):_ -> do
          case nfBody nf of
            Exists d to (App Eq [AppWf d1 [] _, AppWf v1 [] _]) | d == d1 && v == v1 -> do
              case Set.toList to of
                [to] -> do
                  coe <- mkCoercion (Signature name) to
                  pure (IntroSort name : coe, NFTerm [] [] [] (App Top []))
                [] -> pure ([IntroSort name], NFTerm [] [] [] (App Top []))
                (_:_:_) -> failWithMessage $ "The 'from' type of the coercion must be unique!"
            App Top [] -> pure ([IntroSort name], NFTerm [] [] [] (App Top []))
            _ -> failWithMessage $ "The type declaration is malformed! " <> pretty nf
        -- Atoms and signatures.
        (Tag HeadTerm (AppWf name args _)):assms -> do
          (im, ex) <- extractExplicit name (nfImplicit nf) args
          as <- mapM noTags $ reverse assms
          pure ([IntroAtom name im ex as], NFTerm [] [] [] (App Top []))
        (Tag HeadTerm (App Eq [AppWf v0 [] _, AppWf name args _])):assms -> do
          as <- mapM noTags $ reverse assms
          (im, ex) <- extractExplicit name (nfImplicit nf) args
          case nfBody nf of
            Exists d to (App Eq [AppWf d1 [] _, AppWf v1 [] _]) | d == d1 && v0 == v1 -> do
              let im' = List.deleteBy ((==) `on` fst) (v0, mempty) im
              pure ([IntroSignature name to im' ex as], NFTerm [] [] [] (App Top []))
            _ -> failWithMessage $ "The signature is malformed! " <> pretty nf
        _ -> pure ([], nf)
  bdDefs <- case nfBody nf of
        -- TODO: This case does not match when the coercion already exists and thus an error
        -- 'Remaining tag: CoercionTag' is thrown!
        Tag CoercionTag (AppWf to [AppWf v0 [] _] _) ->
          case List.lookup v0 (nfImplicit nf) of
            (Just from) -> do
              case (Set.toList from) of
                ([]) -> failWithMessage $ "The 'from' type of the coercion must be provided!"
                ((_:_:_)) -> failWithMessage $ "The 'from' type of the coercion must be unique!"
                ([from]) -> do
                  coe <- mkCoercion from (Signature to)
                  pure coe
            _ -> failWithMessage $ "Couldn't parse coercion!"
        Tag CoercionTag (Exists _ to (App Eq [_, AppWf v0 [] _])) ->
          case Map.lookup v0 (preBoundVars ctx) of
            (Just from) -> do
              case (Set.toList from, Set.toList to) of
                ([], _) -> failWithMessage $ "The 'from' type of the coercion must be provided!"
                ((_:_:_), _) -> failWithMessage $ "The 'from' type of the coercion must be unique!"
                (_, []) -> failWithMessage $ "The 'to' type of the coercion must be provided!"
                (_, (_:_:_)) -> failWithMessage $ "The 'to' type of the coercion must be unique!"
                ([from], [to]) -> do
                  coe <- mkCoercion from to
                  pure coe
            _ -> failWithMessage $ "Couldn't parse coercion!"
        -- predicate definitions
        App Iff [Tag HeadTerm (AppWf name args _), def] -> do
          as <- mapM noTags $ nfAssumptions nf
          b <- noTags $ def
          (im, ex) <- extractExplicit name (nfImplicit nf) args
          pure [Predicate name $ NFTerm im ex as b]
        Forall v0 m (App Iff [Tag HeadTerm (AppWf name ((AppWf v1 [] _):args) _), def]) | v0 == v1 -> do
          as <- mapM noTags $ nfAssumptions nf
          b <- noTags $ def
          (im, ex) <- extractExplicit name (nfImplicit nf) args
          pure [Predicate name $ NFTerm im ((v0, m):ex) as b]
        -- function definitions
        Forall _ retval (App Iff [Tag HeadTerm (App Eq [_, AppWf name args _]), App Eq [_, def]]) -> do
          as <- mapM noTags $ nfAssumptions nf
          b <- noTags $ def
          (im, ex) <- extractExplicit name (nfImplicit nf) args
          pure [Function name retval $ NFTerm im ex as b]
        Forall _ retval (App Imp [Tag HeadTerm (App Eq [AppWf v0 [] _, AppWf name args _]), def]) -> do
          as <- mapM noTags $ nfAssumptions nf
          b <- noTags $ def
          (im, ex) <- extractExplicit name (nfImplicit nf) args
          case b of
            Exists d to (App Eq [AppWf d1 [] _, AppWf v1 [] _]) | d == d1 && v0 == v1 -> do
              let im' = List.deleteBy ((==) `on` fst) (v0, mempty) im
              pure [IntroSignature name to im' ex as]
            _ -> pure [Function name retval $ NFTerm im ex as b]
        _ -> do
          as <- mapM noTags (nfAssumptions nf)
          b <- noTags $ nfBody nf
          if b /= App Top []
            then pure [Axiom (NFTerm (nfImplicit nf) [] as b)]
            else pure []
  pure $ asDefs ++ bdDefs

-- | Convert a block into a statement.
transformBlock :: Message.Comm m => Context -> Block -> Err m [Located (Stmt Set ())]
transformBlock ctx bl@(Block f b _ _ n l _) = map (Located n (position bl)) <$>
  case f of
    -- top-level blocks:
    (F.Var (VarHole _) _ _) -> do
      gottenBlocks <- reverse <$> concat <$> mapM getBlocks b
      case gottenBlocks of
        [] -> failWithMessage "Internal error: list of blocks is empty"
        (main:assms) -> do
          let mainF = foldl (flip F.Imp) (formula main) (formula <$> assms)
          mainT <- parseFormula mainF >>= extractGivenTypes ctx . bindAllExcept (Set.union (sorts ctx) $ Map.keysSet $ preBoundVars ctx)
          let mainT' = termToNF mainT
          case Block.needsProof bl of
            True -> do
              nfT <- noTags mainT
              nfT' <- checkNF $ termToNF nfT
              (:[]) <$> Claim nfT' <$> (convertProof l (preBind (Map.fromList $ nfImplicit nfT') ctx) (body main))
            False -> extractDefinitions ctx mainT'
    _ -> failWithMessage "Internal: transformBlock should not be applied to proofs!"

transform :: Message.Comm m => [ProofText] -> m [Located (Stmt Set ())]
transform = flip evalStateT initErrors
  . go mempty . concatMap (\case ProofTextBlock bl -> [bl]; _ -> [])
  where
    initErrors = ErrorContext undefined F.Top noSourcePos

    go _ [] = pure []
    go c (b:bs) = do
      modify $ \s -> s { errorBlock = b }
      modify $ \s -> s { errorPosition = position b }
      stmts <- transformBlock c b
      (stmts ++) <$> go (List.foldl' updateCtx c stmts) bs

    updateCtx ctx@(Context idents pbv) (Located _ _ s) = case s of
      IntroSort n -> Context (Set.insert n idents) pbv
      IntroAtom n _ _ _ -> Context idents (Map.insert n mempty pbv)
      IntroSignature n _ _ _ _ -> Context idents (Map.insert n mempty pbv)
      Predicate n _ -> Context idents (Map.insert n mempty pbv)
      Function n _ _ -> Context idents (Map.insert n mempty pbv)
      _ -> ctx
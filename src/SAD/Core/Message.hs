{-
Authors: Makarius Wenzel (2018)

Formal output messages, with PIDE (Prover IDE) support.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}

module SAD.Core.Message (
  PIDE, pideContext, pideActive,
  initThread, exitThread, consoleThread,
  Kind (..), entityMarkup,
  Report, ReportText, reportsText, reportText, reports, report,
  trimText, output, error, outputMain, outputExport, outputForTheL,
  outputParser, outputReasoner, outputThesis, outputSimplifier, outputTranslate,
  errorExport, errorParser
) where

import Prelude hiding (error)
import qualified Prelude (error)
import System.Environment
import Control.Monad
import Data.Maybe
import Data.IORef
import System.IO.Unsafe
import Data.ByteString (ByteString)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Char8 as Char8
import qualified Data.ByteString.UTF8 as UTF8
import Control.Concurrent (ThreadId)
import qualified Control.Concurrent as Concurrent
import Network.Socket (Socket)

import SAD.Core.SourcePos (SourcePos)
import qualified SAD.Core.SourcePos as SourcePos

import Isabelle.Library as Isabelle
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Value as Value
import qualified Isabelle.Markup as Markup
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Naproche as Naproche


-- PIDE thread context

data PIDE = PIDE {pideID :: String, pideFile :: String, pideShift :: Int}
type Channel = [ByteString] -> IO ()
data Context = Context {pide :: Maybe PIDE, channel :: Channel}

defaultChannel :: Channel
defaultChannel = Char8.putStrLn . ByteString.concat

defaultContext :: Context
defaultContext = Context Nothing defaultChannel

  
-- global state

type Threads = Map ThreadId Context

{-# NOINLINE globalState #-}
globalState :: IORef Threads
globalState = unsafePerformIO (newIORef Map.empty)

getContext :: IO Context
getContext = do
  id <- Concurrent.myThreadId
  threads <- readIORef globalState
  return (fromMaybe defaultContext (Map.lookup id threads))

updateState :: (ThreadId -> Threads -> Threads) -> IO ()
updateState f = do
  id <- Concurrent.myThreadId
  atomicModifyIORef' globalState (\threads -> (f id threads, ()))


-- PIDE context

pideContext :: IO (Maybe PIDE)
pideContext = pide <$> getContext

pideActive :: IO Bool
pideActive = isJust <$> pideContext


-- init/exit thread context

initThread :: Properties.T -> Channel -> IO ()
initThread props channel = do
  let property parse = Properties.get_value parse props
  let pideProperty = property proper_string Naproche.naproche_pide
  let fileProperty = property Just Naproche.naproche_pos_file
  let shiftProperty = property Value.parse_int Naproche.naproche_pos_shift
  let
    pideContext =
      case (pideProperty, fileProperty, shiftProperty) of
        (Just pide, Just file, Just shift) -> Just (PIDE pide file shift)
        _ -> Nothing
  updateState (\id -> Map.insert id (Context pideContext channel))

exitThread :: IO ()
exitThread = updateState Map.delete

consoleThread :: IO ()
consoleThread = do
  env <- getEnvironment
  initThread env defaultChannel


-- PIDE messages

data Kind =
  STATE | WRITELN | INFORMATION | TRACING | WARNING | LEGACY | ERROR

instance Show Kind where
  show WARNING = "Warning"
  show LEGACY = "Legacy feature"
  show ERROR = "Error"
  show _ = ""

kindXML :: Kind -> String
kindXML STATE = Markup.stateN
kindXML WRITELN = Markup.writelnN
kindXML INFORMATION = Markup.informationN
kindXML TRACING = Markup.tracingN
kindXML WARNING = Markup.warningN
kindXML LEGACY = Markup.legacyN
kindXML ERROR = Markup.errorN

posProperties :: PIDE -> SourcePos -> [(String, String)]
posProperties PIDE{pideID, pideFile, pideShift} pos =
  (if null pideID then [] else [(Markup.idN, pideID)]) ++
  (if null file then [] else [(Markup.fileN, file)]) ++
  (if line <= 0 then [] else [(Markup.lineN, Value.print_int line)]) ++
  (if offset <= 0 then [] else [(Markup.offsetN, Value.print_int offset)]) ++
  (if endOffset <= 0 then [] else [(Markup.end_offsetN, Value.print_int endOffset)])
  where
    file =
      case SourcePos.sourceFile pos of
        "" -> pideFile
        file -> file
    line = if null file then 0 else SourcePos.sourceLine pos
    shift i = if i <= 0 then i else i + pideShift
    offset = shift $ SourcePos.sourceOffset pos
    endOffset = shift $ SourcePos.sourceEndOffset pos

posDefProperties :: PIDE -> SourcePos -> [(String, String)]
posDefProperties pide = map (\(a, b) -> ("def_" ++ a, b)) . posProperties pide

entityProperties :: PIDE -> Bool -> Int -> SourcePos -> [(String, String)]
entityProperties pide def serial pos =
  if def then (Markup.defN, Value.print_int serial) : posProperties pide pos
  else (Markup.refN, Value.print_int serial) : posDefProperties pide pos

entityMarkup :: PIDE -> String -> String -> Bool -> Int -> SourcePos -> Markup.T
entityMarkup pide kind name def serial pos =
    Markup.properties (entityProperties pide def serial pos) (Markup.entity kind name)

xmlMessage :: PIDE -> String -> Kind -> SourcePos -> String -> XML.Tree
xmlMessage pide origin kind pos msg =
  XML.Elem ((kindXML kind, props), [XML.Text msg])
  where
    props0 = posProperties pide pos
    props = if null origin then props0 else (Naproche.origin, origin) : props0

pideMessage :: String -> [ByteString]
pideMessage = Byte_Message.make_line_message . UTF8.fromString


-- PIDE markup reports

type Report = (SourcePos, Markup.T)
type ReportText = (Report, String)

reportsText :: [ReportText] -> IO ()
reportsText args = do
  context <- getContext
  when (isJust (pide context) && not (null args)) $
    channel context $ pideMessage $ YXML.string_of $
      XML.Elem (Markup.report,
        map (\((pos, markup), txt) ->
          let
            markup' = Markup.properties (posProperties (fromJust (pide context)) pos) markup
            body = if null txt then [] else [XML.Text txt]
          in XML.Elem (markup', body)) args)

reportText :: SourcePos -> Markup.T -> String -> IO ()
reportText pos markup txt = reportsText [((pos, markup), txt)]

reports :: [Report] -> IO ()
reports = reportsText . map (, "")

report :: SourcePos -> Markup.T -> IO ()
report pos markup = reports [(pos, markup)]


-- output

trimText :: String -> String
trimText = Isabelle.trim_line

messageBytes :: Maybe PIDE -> String -> Kind -> SourcePos -> String -> [ByteString]
messageBytes pide origin kind pos msg =
  if isJust pide then
    pideMessage $ YXML.string_of $ xmlMessage (fromJust pide) origin kind pos msg
  else
    [UTF8.fromString
      ((if null origin then "" else "[" ++ origin ++ "] ") ++
       (case show kind of "" -> "" ; s -> s ++ ": ") ++
       (case show pos of "" -> ""; s -> s ++ "\n") ++ msg)]

output :: String -> Kind -> SourcePos -> String -> IO ()
output origin kind pos msg = do
  context <- getContext
  channel context $ messageBytes (pide context) origin kind pos msg

error :: String -> SourcePos -> String -> IO a
error origin pos msg = do
  pide <- pideContext
  errorWithoutStackTrace $
    UTF8.toString $ ByteString.concat $ messageBytes pide origin ERROR pos msg


-- specific messages

outputMain, outputExport, outputForTheL, outputParser, outputReasoner,
  outputSimplifier, outputThesis :: Kind -> SourcePos -> String -> IO ()
outputMain = output Naproche.origin_main
outputExport = output Naproche.origin_export
outputForTheL = output Naproche.origin_forthel
outputParser = output Naproche.origin_parser
outputReasoner = output Naproche.origin_reasoner
outputSimplifier = output Naproche.origin_simplifier
outputThesis = output Naproche.origin_thesis
outputTranslate = output Naproche.origin_translate

errorExport = error Naproche.origin_export
errorParser = error Naproche.origin_parser

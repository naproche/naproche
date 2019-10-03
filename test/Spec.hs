module Main where

import Data.List
import System.Process
import System.Exit
import GHC.IO.Handle
import Control.Arrow
import Control.Monad
import Control.Concurrent

compileFile :: FilePath -> IO (Handle, ProcessHandle)
compileFile f = do
  (_, Just hout, _, ph) <- createProcess (proc "stack" ["exec", "Naproche-SAD", "--", f, "-t", "20"])
    { std_out = CreatePipe }
  pure (hout, ph)

gather :: (Handle, ProcessHandle) -> IO (ExitCode, String)
gather (hout, ph) = do
  code <- waitForProcess ph
  cont <- hGetContents hout
  pure (code, cont)

files :: [FilePath]
files = map ("examples/"++) $
  [ "chinese.ftl"
  , "fuerst.ftl"
  , "Koenigs_lemma.ftl"
  , "Maximum_principle.ftl"
  , "newman.ftl"
  , "powerset.ftl"
  , "prime_no_square.ftl"
  , "regular_successor.ftl"
  , "tarski.ftl"
  ]

output :: [(FilePath, (ExitCode, String))] -> IO (ExitCode, [FilePath])
output xs = do
  mapM_ (putStrLn . snd . snd) xs
  let code = foldl' max ExitSuccess $ map (fst . snd) xs
  let failed = map fst $ filter ((/=ExitSuccess) . fst . snd) xs
  pure (code, failed)

main :: IO ()
main = do
  (code, failed) <- output . zip files =<< mapM gather =<< mapM compileFile files
  when (not $ null failed) $ do
    putStrLn $ "Failed to compile: " ++ unwords failed
  exitWith code

module Main where

import Data.List
import System.Process
import System.Exit
import System.IO
import Data.IORef
import Control.Monad
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy.IO as TIO

compileFile :: FilePath -> IO (Handle, Handle, ProcessHandle)
compileFile f = do
  -- TODO: Add tex file examples!!
  (_, Just hout, Just herr, ph) <- createProcess (proc "stack" ["exec", "Naproche-SAD", "--", f, "-t", "25"])
    { std_out = CreatePipe, std_err = CreatePipe }
  pure (hout, herr, ph)

gather :: (Handle, Handle, ProcessHandle) -> IO (ExitCode, Text)
gather (hout, herr, ph) = do
  code <- waitForProcess ph
  cont <- TIO.hGetContents hout
  _ <- TIO.hGetContents herr
  pure (code, cont)

files :: [FilePath]
files = fmap ("examples/"++)
  -- This file does check, but it often fails when limited to reasonable time
  -- [ "chinese.ftl"
  [ "fuerst.ftl"
  , "Koenigs_lemma.ftl"
  , "Maximum_principle.ftl"
  , "newman.ftl"
  , "powerset.ftl"
  , "prime_no_square.ftl"
  , "regular_successor.ftl"
  , "tarski.ftl"
  , "inconsistency.ftl"
  ]

shouldFailFiles :: [FilePath]
shouldFailFiles = map ("examples/"++) $
  [ "inconsistency.ftl" 
  ]

output :: [(FilePath, (ExitCode, Text))] -> IO [(ExitCode, FilePath)]
output xs = do
  mapM_ (TIO.putStrLn . snd . snd) xs
  let failed = map (\(f, (c, _)) -> (c, f)) $ filter ((/=ExitSuccess) . fst . snd) xs
  pure failed

main :: IO ()
main = do
  failed <- output . zip files =<< mapM gather =<< mapM compileFile files
  let shouldntHaveFailed = filter (\f -> snd f `notElem` shouldFailFiles) failed
  let shouldHaveFailed = shouldFailFiles \\ map snd failed
  code <- newIORef ExitSuccess
  when (not $ null shouldntHaveFailed) $ do
    putStrLn $ "Failed to compile: " ++ unwords (map snd $ shouldntHaveFailed)
    writeIORef code $ foldl' max ExitSuccess $ map fst shouldntHaveFailed
  when (not $ null shouldHaveFailed) $ do
    putStrLn $ "Compiled even though it shouldn't: " ++ unwords shouldHaveFailed
    writeIORef code (ExitFailure 1)
  readIORef code >>= exitWith

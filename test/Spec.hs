module Main where

import Data.List
import System.Process
import System.Exit
import System.IO
import Data.IORef
import Control.Monad
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy.IO as TIO

compileFile :: [String] -> FilePath -> IO (Handle, Handle, ProcessHandle)
compileFile flags f = do
  (_, Just hout, Just herr, ph) <- createProcess (proc "stack" (["exec", "Naproche-SAD", "--", f] ++ flags))
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
  [ "chinese.ftl"
  , "fuerstenberg.ftl"
  , "maximum_modulus.ftl"
  , "newman.ftl"
  , "cantor.ftl"
  , "prime_no_square.ftl"
  , "tarski.ftl"
  ] ++ [
   "test/examples/read_test.ftl"
  ]

texFiles :: [FilePath]
texFiles = fmap ("examples/"++)
  [ "checkerboard.ftl.tex"
  , "chinese.ftl.tex"
  , "fuerstenberg.ftl.tex"
  , "maximum_modulus.ftl.tex"
  , "newman.ftl.tex"
  , "cantor.ftl.tex"
  , "prime_no_square.ftl.tex"
  , "tarski.ftl.tex"
  ] ++ fmap ("text/examples/"++)
  [ "read_test.ftl.tex"
  , "lambda_term_test.ftl.tex"
  , "text.ftl.tex"
  , "varprime.ftl.tex"
  ]

output :: [(FilePath, (ExitCode, Text))] -> IO [(ExitCode, FilePath)]
output xs = do
  mapM_ (TIO.putStrLn . snd . snd) xs
  let failed = map (\(f, (c, _)) -> (c, f)) $ filter ((/=ExitSuccess) . fst . snd) xs
  pure failed

main :: IO ()
main = do
  compiled <- mapM (\f -> gather =<< compileFile ["--tex=off"] f) files
  compiledTex <- mapM (\f -> gather =<< compileFile ["--tex=on"] f) texFiles

  failed <- output . zip (files ++ texFiles) $ (compiled ++ compiledTex)
  code <- newIORef ExitSuccess
  unless (null failed) $ do
    putStrLn $ "Failed to compile: " ++ unwords (map snd failed)
    writeIORef code $ foldl' max ExitSuccess $ map fst failed
  readIORef code >>= exitWith

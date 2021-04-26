module Main where

import Data.List
import System.Process
import System.Exit
import System.IO
import Data.IORef
import Control.Monad
import Data.Text (Text)
import qualified Data.Text.IO as TIO

compileFile :: [String] -> FilePath -> IO (Handle, Handle, ProcessHandle)
compileFile flags f = do
  (_, Just hout, Just herr, ph) <- createProcess (proc "stack" (["exec", "Naproche-SAD", "--", f, "-T"] ++ flags))
    { std_out = CreatePipe, std_err = CreatePipe }
  pure (hout, herr, ph)

gather :: (Handle, Handle, ProcessHandle) -> IO (ExitCode, String)
gather (hout, herr, ph) = do
  code <- waitForProcess ph
  cont <- hGetContents hout
  err <- hGetContents herr
  pure (code, cont <> err)

texFiles :: [FilePath]
texFiles = fmap ("../lib/examples/"++)
  [ "cantor.ftl.tex"
  , "checkerboard.ftl.tex"
  , "chinese.ftl.tex"
  , "fuerstenberg.ftl.tex"
  , "koenig.ftl.tex"
  , "maximum_modulus.ftl.tex"
  , "newman.ftl.tex"
  , "cantor.ftl.tex"
  , "prime_no_square.ftl.tex"
  , "regular_successor.ftl.tex"
  , "tarski.ftl.tex"
  ]

output :: [(FilePath, (ExitCode, String))] -> IO [(ExitCode, FilePath)]
output xs = do
  mapM_ (putStrLn . snd . snd) xs
  let failed = map (\(f, (c, _)) -> (c, f)) $ filter ((/=ExitSuccess) . fst . snd) xs
  pure failed

main :: IO ()
main = do
  compiledTex <- mapM (\f -> gather =<< compileFile ["--tex=on"] f) texFiles

  failed <- output $ zip texFiles compiledTex
  code <- newIORef ExitSuccess
  unless (null failed) $ do
    putStrLn $ "Failed to compile: " ++ unwords (map snd failed)
    writeIORef code $ foldl' max ExitSuccess $ map fst failed
  readIORef code >>= exitWith

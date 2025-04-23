-- |
-- Module      : SAD.Render.PDF
-- Copyright   : (c) 2025, Marcel Schütz
-- License     : GPL-3
--
-- Render ForTheL Texts as PDF


{-# LANGUAGE OverloadedStrings #-}

module SAD.Render.PDF (
  renderFile,
  renderArchive
) where

import Control.Monad (filterM)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Maybe qualified as Maybe
import Data.Bifunctor qualified as Bifunctor
import Data.Map (Map)
import Data.Map qualified as Map
import Data.List.Split (splitOn)
import System.Directory
import System.Process (callCommand)
import System.FilePath

import SAD.Helpers (getFormalizationsDirectoryPath)

import Naproche.Program qualified as Program

import Isabelle.Library
import Isabelle.File qualified as File

-- | Render a TeX file to PDF.
renderFile :: Program.Context -> FilePath -> IO Int
renderFile context filePath = do
  putStrLn "[Warning] This is an experimental feature. Please be gentle.\n"
  formalizationsDirectoryPath <- getFormalizationsDirectoryPath context

  -- Set the paths to pdflatex and bibtex, and the MATHHUB and TEXINPUTS variable:
  let pdflatexBin = "pdflatex"
      bibtexBin = "bibtex"
      mathhubVar = formalizationsDirectoryPath
      texinputsVar = formalizationsDirectoryPath </> "latex" </> "lib//;" 
  putStrLn $ "[Info] Path to pdflatex:   " ++ pdflatexBin
  putStrLn $ "[Info] Path to bibtex:     " ++ bibtexBin
  putStrLn $ "[Info] MATHHUB variable:   " ++ mathhubVar
  putStrLn $ "[Info] TEXINPUTS variable: " ++ texinputsVar

  -- Render the input file as PDF:
  let inputDir = takeDirectory filePath
      inputFile = takeFileName filePath
      inputFileBase = takeBaseName inputFile
  setCurrentDirectory inputDir
  callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_WRITESMS=true " ++ pdflatexBin ++ " " ++ inputFile
  callCommand $ bibtexBin ++ " " ++ inputFileBase ++ " | true" -- succeed even if bibtex fails
  callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_USESMS=true " ++ pdflatexBin ++ " " ++ inputFile
  callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_USESMS=true " ++ pdflatexBin ++ " " ++ inputFile

  return 0


-- | Render all TeX files in the @source@ directory of an sTeX archive as one
-- single PDF.
renderArchive :: Program.Context -> String -> IO Int
renderArchive context archiveId = do
  putStrLn "[Warning] This is an experimental feature. Please be gentle.\n"
  formalizationsDirectoryPath <- getFormalizationsDirectoryPath context
  let archiveComponents = splitOn "/" archiveId
      archiveName = last archiveComponents
      archiveDirPath = formalizationsDirectoryPath </> joinPath archiveComponents
      manifestFilePath = archiveDirPath </> "META-INF" </> "MANIFEST" <.> "MF"
      sourceDirPath = archiveDirPath </> "source"
  doesManifestFileExist <- doesFileExist manifestFilePath
  if doesManifestFileExist
    then do
      manifestContent <- make_text <$> File.read manifestFilePath
      let manifestEntries = readManifest manifestContent
          mbTitle = Map.lookup "title" manifestEntries
          mbAuthor = Map.lookup "authors" manifestEntries
          mbLicense = Map.lookup "license" manifestEntries
      title <- case mbTitle of
        Just title -> pure $ "\\title{" <> title <> "}"
        Nothing -> do
          putStrLn $
            "[Warning] No \"title\" entry provided in\n" ++
            "          \"" ++ manifestFilePath ++ "\".\n" ++
            "          Therefore, no title will be printed."
          return "\\title{}"
      author <- case mbAuthor of
        Just author -> pure $ "\\author{" <> author <> "}"
        Nothing -> do
          putStrLn $
            "[Warning] No \"authors\" entry provided in\n" ++
            "          \"" ++ manifestFilePath ++ "\".\n" ++
            "          Therefore, no author names will be printed."
          return "\\author{}"
      let date = "\\date{}"
      license <- case mbAuthor of
        Nothing -> do
          putStrLn $
            "[Warning] No \"authors\" entry provided in\n" ++
            "          \"" ++ manifestFilePath ++ "\".\n" ++
            "          Therefore, no license or copyright notification will be printed."
          return ""
        Just author -> case mbLicense of
          Just "CcZero" -> pure $ "\\printlicense[CcZero]{" <> author <> "}"
          Just "CcBy" -> pure $ "\\printlicense[CcBy]{" <> author <> "}"
          Just "CcBySa" -> pure $ "\\printlicense[CcBySa]{" <> author <> "}"
          Just "CcByNc" -> pure $ "\\printlicense[CcByNc]{" <> author <> "}"
          Just "CcByNcSa" -> pure $ "\\printlicense[CcByNcSa]{" <> author <> "}"
          Just "CcByNd" -> pure $ "\\printlicense[CcByNd]{" <> author <> "}"
          Just "CcByNcNd" -> pure $ "\\printlicense[CcByNcNd[{" <> author <> "}"
          Just license -> do
            putStrLn $
              "[Warning] Invalid value \"" ++ Text.unpack license ++ "\" for key \"license\" in\n" ++
              "          \"" ++ manifestFilePath ++ "\".\n" ++
              "          The following are allowed:\n" ++
              "            - \"CcZero\" (CC0 1.0)\n" ++
              "            - \"CcBy\" (CC BY 4.0)\n" ++
              "            - \"CcBySa\" (CC BY-SA 4.0)\n" ++
              "            - \"CcByNc\" (CC BY-NC 4.0)\n" ++
              "            - \"CcByNcSa\" (CC BY-NC-SA 4.0)\n" ++
              "            - \"CcByNd\" (CC BY-ND 4.0)\n" ++
              "            - \"CcByNcNd\" (CC BY-NC-ND 4.0)\n" ++
              "          Therefore, no license notification will be printed."
            return ""
          Nothing -> pure $ "\\printcopyright{" <> author <> "}"
      
      sourceFiles <- gatherFtlTexFiles sourceDirPath ""
      let sourceFiles' = filter (/= (Text.pack archiveName <> ".ftl.tex")) sourceFiles
      let inputrefs = map (\fileLocation -> "\\inputref[" <> Text.pack archiveId <> "]{" <> fileLocation <> "}") sourceFiles'

      let texContent =
            "% This file was automatically generated by Naproche.\n" <>
            "\n" <>
            "\\documentclass[numberswithinsection]{naproche-library}\n" <>
            "\n" <>
            "\\libinput[latex]{archive}\n" <>
            "\\libinput[" <> Text.pack archiveId <> "]{preamble}\n" <>
            "\n" <>
            title <> "\n" <>
            author <> "\n" <>
            date <> "\n" <>
            "\n" <>
            "\\begin{document}\n" <>
            "  \\maketitle\n" <>
            "  \\tableofcontents\n" <>
            "  \\setsectionlevel{section}\n" <>
            "  " <> Text.intercalate "\n  " inputrefs <> "\n" <>
            (if Text.null license then "" else "  " <> license <> "\n") <>
            "\\end{document}"

      -- Generate the TeX file:
      let texFilePath = sourceDirPath </> archiveName <.> "ftl" <.> "tex"
      writeFile texFilePath (Text.unpack texContent)
      putStrLn $ "[Info] Generated TeX file: " ++ texFilePath

       -- Set the paths to pdflatex and bibtex, and the MATHHUB and TEXINPUTS variable:
      let pdflatexBin = "pdflatex"
          bibtexBin = "bibtex"
          mathhubVar = formalizationsDirectoryPath
          texinputsVar = formalizationsDirectoryPath </> "latex" </> "lib//;" 
      putStrLn $ "[Info] Path to pdflatex:   " ++ pdflatexBin
      putStrLn $ "[Info] Path to bibtex:     " ++ bibtexBin
      putStrLn $ "[Info] MATHHUB variable:   " ++ mathhubVar
      putStrLn $ "[Info] TEXINPUTS variable: " ++ texinputsVar

      -- Render the TeX file as PDF:
      let inputDir = takeDirectory texFilePath
          inputFile = takeFileName texFilePath
          inputFileBase = takeBaseName inputFile
      setCurrentDirectory inputDir
      callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_WRITESMS=true " ++ pdflatexBin ++ " " ++ inputFile
      callCommand $ bibtexBin ++ " " ++ inputFileBase ++ " | true" -- succeed even if bibtex fails
      callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_USESMS=true " ++ pdflatexBin ++ " " ++ inputFile
      callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_USESMS=true " ++ pdflatexBin ++ " " ++ inputFile
      
      let pdfFilePath = sourceDirPath </> archiveName <.> "ftl" <.> "pdf"
      putStrLn $ "[Info] Generated PDF file: " ++ pdfFilePath
      return 0
    else do
      putStrLn $ "[Error] File \"" ++ manifestFilePath ++ "\" not found."
      return 1


-- | Collect all TeX files in a directory and, recursively, all its
-- subdirectories.
gatherFtlTexFiles :: FilePath -> FilePath -> IO [Text]
gatherFtlTexFiles absoluteDirPath relativeDirPath = do
  dirEntries <- listDirectory absoluteDirPath
  fileNames <- filterM (\fileName -> doesFileExist (absoluteDirPath </> fileName)) dirEntries
  let ftlTexFileNames = filter (".ftl.tex" `isExtensionOf`) fileNames
      ftlTexFilePaths = if null relativeDirPath then ftlTexFileNames else map (relativeDirPath </>) ftlTexFileNames
      ftlTexFilePathComponents = map splitDirectories ftlTexFilePaths
      ftlTexFileLocations = map (Text.intercalate "/" . map Text.pack) ftlTexFilePathComponents
  subDirNames <- filterM (\dirName -> doesDirectoryExist (absoluteDirPath </> dirName)) dirEntries
  let newPaths = map (\subDirName -> (absoluteDirPath </> subDirName, relativeDirPath </> subDirName)) subDirNames
  ftlTexFilesInSubDirs <- concat <$> mapM (uncurry gatherFtlTexFiles) newPaths
  return $ ftlTexFileLocations ++ ftlTexFilesInSubDirs


-- | Read the content of a @MANIFEST.MF@ file into a key-value map.
readManifest :: Text -> Map Text Text
readManifest fileContent =
  let lines = Text.lines fileContent
      keyValPairs = map (Text.span (/= ':')) lines
      keyMbValPairs = map (\(k,v) -> (k, if Text.length v > 0 then Just (Text.tail v) else Nothing)) keyValPairs
      filteredKeyValPairs = map (Bifunctor.second Maybe.fromJust) $ filter (\(k,v) -> Maybe.isJust v) keyMbValPairs
      strippedKeyValPairs = map (Bifunctor.bimap Text.strip Text.strip) filteredKeyValPairs
  in Map.fromList strippedKeyValPairs

-- |
-- Module      : SAD.Export.Render
-- Copyright   : (c) 2025, Marcel Schütz
-- License     : GPL-3
--
-- Render ForTheL Texts as PDF or HTML


{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.Render (
  Format(..),
  renderFile,
  renderLibrary
) where

import Control.Monad (filterM, when)
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
import System.IO
import Text.Regex.TDFA


import SAD.Helpers (getFormalizationsDirectoryPath)

import Naproche.Program qualified as Program

import Isabelle.Library
import Isabelle.File qualified as File


-- * Rendering Formats

data Format = PDF | HTML deriving (Eq)

instance Show Format where
  show :: Format -> String
  show PDF = "PDF"
  show HTML = "HTML"


-- * Rendering Single TeX Files

-- | Render a TeX file.
renderFile :: Format -> Program.Context -> FilePath -> IO Int
renderFile format context filePath = do
  putStrLn "[Warning] This is an experimental feature. Please be gentle."
  formalizationsDirectoryPath <- getFormalizationsDirectoryPath context

  -- Set the paths to pdflatex, bibtex and rustex, and the MATHHUB and TEXINPUTS variable:
  let pdflatexBin = "pdflatex"
      bibtexBin = "bibtex"
      rustexBin = "rustex"
      mathhubVar = formalizationsDirectoryPath
      texinputsVar = formalizationsDirectoryPath </> "latex" </> "lib//;"
      cssFilePath = formalizationsDirectoryPath </> "latex" </> "lib" </> "naproche" <.> "css"

  putStrLn ""
  case format of
    PDF ->  putStrLn $ "[Info] Make sure that " ++ pdflatexBin ++ " and " ++ bibtexBin ++ " are in your PATH."
    HTML ->  putStrLn $ "[Info] Make sure that " ++ pdflatexBin ++ ", " ++ rustexBin ++ " and " ++ bibtexBin ++ " are in your PATH."

  putStrLn ""
  putStrLn $ "[Info] MATHHUB variable set to:   " ++ mathhubVar
  putStrLn $ "[Info] TEXINPUTS variable set to: " ++ texinputsVar
  when (format == HTML) $ putStrLn $ "[Info] Naproche CSS file:         " ++ cssFilePath

  putStrLn ""
  putStrLn $ "Ready to render \"" ++ filePath ++ "\" to " ++ show format ++ "."
  putStrLn "Do you want to continue? (Y/n)"
  answer <- getLine

  if answer `elem` ["Y", "y", ""]
    -- Render the input file:
    then do
      let inputDir = takeDirectory filePath
          inputFile = takeFileName filePath
          inputFileBase = takeBaseName inputFile
          pdfFile = inputFileBase <.> "pdf"
          htmlFile = inputFileBase <.> "xhtml"
          outputFile = case format of
            PDF -> pdfFile
            HTML -> htmlFile
          outputFilePath = inputDir </> outputFile
      setCurrentDirectory inputDir
      case format of
        PDF -> do
          callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_WRITESMS=true " ++ pdflatexBin ++ " " ++ inputFile
          callCommand $ bibtexBin ++ " " ++ inputFileBase ++ " | true" -- succeed even if bibtex fails
          callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_USESMS=true " ++ pdflatexBin ++ " " ++ inputFile
          callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_USESMS=true " ++ pdflatexBin ++ " " ++ inputFile
        HTML -> do
          -- Check if a PDF file already exists and if so, rename it so that it
          -- can be restored after the HTML build process:
          pdfFileAlreadyExisted <- doesFileExist pdfFile
          let pdfBackupFile = pdfFile ++ "~"
          when pdfFileAlreadyExisted $ renameFile pdfFile pdfBackupFile

          callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_WRITESMS=true " ++ pdflatexBin ++ " " ++ inputFile -- to generate <inputFileBase>.aux
          callCommand $ bibtexBin ++ " " ++ inputFileBase ++ " | true" -- succeed even if bibtex fails
          callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" " ++ rustexBin ++ " -i " ++ inputFile ++ " -o " ++ outputFile
          
          -- Get the content of the HTML file:
          absoluteOutputFilePath <- makeAbsolute outputFile
          
          outputFileHandle <- openFile absoluteOutputFilePath ReadMode
          outputFileContent <- hGetContents' outputFileHandle
          
          -- Get the content of the Naproche CSS file:
          absoluteCssFilePath <- makeAbsolute cssFilePath
          cssFileHandle <- openFile absoluteCssFilePath ReadMode
          cssFileContent <- hGetContents' cssFileHandle

          -- Remove all "rustex:sourceref" attributes and add CSS:
          let sourcerefAttributes = getAllTextMatches (outputFileContent =~ ("rustex:sourceref=\"[^\"]*\"" :: String))
              outputFileContent' = removeAllSubstrings sourcerefAttributes outputFileContent
              outputFileContent'' = insertBeforeFstSubstring "    </style>" cssFileContent outputFileContent'

          -- Replace the content of the HTML file with the altered content:
          writeFile absoluteOutputFilePath outputFileContent''

          -- Remove the generated PDF file and if there was a PDF file before
          -- the HTML build process, restore it:
          removeFile pdfFile
          when pdfFileAlreadyExisted $ renameFile pdfBackupFile pdfFile

      -- Clean up:
      let blxBibFile = inputFileBase ++ "-blx" <.> "bib"
      blxBibFileExists <- doesFileExist blxBibFile
      when blxBibFileExists $ removeFile blxBibFile
      let auxFile = inputFileBase <.> "aux"
      blxBibFileExists <- doesFileExist auxFile
      when blxBibFileExists $ removeFile auxFile
      let bblFile = inputFileBase <.> "bbl"
      blxBibFileExists <- doesFileExist bblFile
      when blxBibFileExists $ removeFile bblFile
      let blgFile = inputFileBase <.> "blg"
      blxBibFileExists <- doesFileExist blgFile
      when blxBibFileExists $ removeFile blgFile
      let logFile = inputFileBase <.> "log"
      blxBibFileExists <- doesFileExist logFile
      when blxBibFileExists $ removeFile logFile
      let outFile = inputFileBase <.> "out"
      blxBibFileExists <- doesFileExist outFile
      when blxBibFileExists $ removeFile outFile
      let runXmlFile = inputFileBase <.> "run" <.> "xml"
      blxBibFileExists <- doesFileExist runXmlFile
      when blxBibFileExists $ removeFile runXmlFile
      let smsFile = inputFileBase <.> "sms"
      blxBibFileExists <- doesFileExist smsFile
      when blxBibFileExists $ removeFile smsFile
      let srefFile = inputFileBase <.> "sref"
      blxBibFileExists <- doesFileExist srefFile
      when blxBibFileExists $ removeFile srefFile
      let upaFile = inputFileBase <.> "upa"
      blxBibFileExists <- doesFileExist upaFile
      when blxBibFileExists $ removeFile upaFile
      let upbFile = inputFileBase <.> "upb"
      blxBibFileExists <- doesFileExist upbFile
      when blxBibFileExists $ removeFile upbFile

      putStrLn ""
      putStrLn $ "[Info] Generated " ++ show format ++ " file: " ++ outputFilePath
      return 0

    -- Abort:
    else do
      putStrLn ""
      putStrLn "Aborted."
      return 1

-- | @removeAllSubstrings substrings string@ removes all substrings from
-- @string@ that match any element of @substrings@.
removeAllSubstrings :: [String] -> String -> String
removeAllSubstrings ss string = Text.unpack $ removeAllSubstrings' (map Text.pack ss) (Text.pack string)
  where
    removeAllSubstrings' [] text = text
    removeAllSubstrings' (t : ts) text =
      removeAllSubstrings' ts $ Text.replace t "" text

-- | @insertBeforeFstSubstring needle insert haystack@ inserts @insert@ before
-- the first occurence of @needle@ in @haystack@. If @haystack@ does not contain
-- @needle@, @haystack@ is returned unmodified.
insertBeforeFstSubstring :: String -> String -> String -> String
insertBeforeFstSubstring needle insert haystack =
  Text.unpack $ insertBeforeFstSubstring' (Text.pack needle) (Text.pack insert) (Text.pack haystack)
  where
    insertBeforeFstSubstring' needle insert haystack =
      let (prefix, rest) = Text.breakOn needle haystack in
      if Text.null rest
        then haystack
        else prefix <> insert <> rest


-- * Rendering Libraries

-- | Render all TeX files in the @source@ directory of a library as a single
-- document.
renderLibrary :: Program.Context -> String -> IO Int
renderLibrary context archiveId = do
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
        Just title -> pure title
        Nothing -> do
          putStrLn $
            "[Warning] No \"title\" entry provided in\n" ++
            "          \"" ++ manifestFilePath ++ "\".\n" ++
            "          Therefore, no title will be printed."
          return ""
      author <- case mbAuthor of
        Just author -> pure author
        Nothing -> do
          putStrLn $
            "[Warning] No \"authors\" entry provided in\n" ++
            "          \"" ++ manifestFilePath ++ "\".\n" ++
            "          Therefore, no author names will be printed."
          return ""
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
            "\\libinput{preamble}\n" <>
            "\n" <>
            "\\title{" <> title <> "}" <> "\n" <>
            "\\author{" <> author <> "}" <> "\n" <>
            "\\date{}" <> "\n" <>
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
      putStrLn $ "[Info] pdflatex executable: " ++ pdflatexBin
      putStrLn $ "[Info] bibtex executable:   " ++ bibtexBin
      putStrLn $ "[Info] MATHHUB variable:    " ++ mathhubVar
      putStrLn $ "[Info] TEXINPUTS variable:  " ++ texinputsVar

      putStrLn ""
      putStrLn $ "Ready to render \"" ++ texFilePath ++ "\" to PDF."
      putStrLn "Do you want to continue? (Y/n)"
      answer <- getLine

      if answer `elem` ["Y", "y", ""]
        -- Render the input file as PDF:
        then do
          -- Render the TeX file as PDF:
          let inputDir = takeDirectory texFilePath
              inputFile = takeFileName texFilePath
              inputFileBase = takeBaseName inputFile
          setCurrentDirectory inputDir
          callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_WRITESMS=true " ++ pdflatexBin ++ " " ++ inputFile
          callCommand $ bibtexBin ++ " " ++ inputFileBase ++ " | true" -- succeed even if bibtex fails
          callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_USESMS=true " ++ pdflatexBin ++ " " ++ inputFile
          callCommand $ "MATHHUB=\"" ++ mathhubVar ++ "\" TEXINPUTS=\"" ++ texinputsVar ++ "\" STEX_USESMS=true " ++ pdflatexBin ++ " " ++ inputFile
          
          let pdfFilePath = inputDir </> inputFileBase <.> "pdf"
          putStrLn ""
          putStrLn $ "[Info] Generated PDF file: " ++ pdfFilePath
          return 0
        
        -- Abort:
        else do
          putStrLn ""
          putStrLn "Aborted."
          return 1

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

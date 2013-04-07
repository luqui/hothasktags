{-# LANGUAGE PatternGuards #-}

module Main where

import qualified Language.Haskell.Exts.Annotated as L
import System.Environment (getArgs)
import System.IO (hPutStrLn, stderr)
import qualified Data.Map as Map
import qualified Language.Preprocessor.Cpphs as CPP
import Control.Monad (forM, when)
import Data.List (sort)
import Data.Maybe (fromMaybe)
import System.FilePath.Posix (takeFileName)
import System.Console.GetOpt

type Database = Map.Map String (L.Module L.SrcSpanInfo)

data Defn = Defn FilePath Int  -- file, line
    deriving Show

localDecls :: L.Module L.SrcSpanInfo -> Map.Map String Defn
localDecls (L.Module _ _ _ _ decls) = Map.fromList $ concatMap extract decls
    where
    extract (L.TypeDecl _ head _) = extractDeclHead head
    extract (L.TypeFamDecl _ head _) = extractDeclHead head
    extract (L.DataDecl _ _ _ head decls _) = extractDeclHead head ++ concatMap extractQualConDecl decls
    extract (L.GDataDecl _ _ _ head _ decls _) = extractDeclHead head ++ concatMap extractGadtDecl decls
    extract (L.DataFamDecl _ _ head _) = extractDeclHead head
    extract (L.ClassDecl _ _ head _ clsdecls) = extractDeclHead head ++ concatMap extractClassDecl (fromMaybe [] clsdecls)
    extract (L.TypeSig _ names _) = concatMap extractName names
    extract (L.FunBind _ (L.Match _ name _ _ _ : _)) = extractName name
    extract (L.FunBind _ (L.InfixMatch _ _ name _ _ _ : _)) = extractName name
    extract (L.PatBind _ pat _ _ _) = extractPat pat
    extract (L.ForImp _ _ _ _ name _) = extractName name
    extract _ = []

    extractDeclHead (L.DHead _ name _) = extractName name
    extractDeclHead (L.DHInfix _ _ name _) = extractName name
    extractDeclHead (L.DHParen _ head') = extractDeclHead head'

    extractPat (L.PVar _ name) = extractName name
    extractPat (L.PApp _ _ pats) = concatMap extractPat pats
    extractPat (L.PTuple _ pats) = concatMap extractPat pats
    extractPat (L.PList _ pats) = concatMap extractPat pats
    extractPat (L.PParen _ pat) = extractPat pat
    extractPat (L.PAsPat _ name pat) = extractName name ++ extractPat pat
    extractPat (L.PIrrPat _ pat) = extractPat pat
    extractPat (L.PatTypeSig _ pat _) = extractPat pat
    extractPat (L.PBangPat _ pat) = extractPat pat
    extractPat _ = []

    extractQualConDecl (L.QualConDecl _ _ _ (L.ConDecl _ name _)) = extractName name
    extractQualConDecl (L.QualConDecl _ _ _ (L.RecDecl _ name fields)) = extractName name ++ concatMap extractFieldDecl fields
    extractQualConDecl _ = []

    extractFieldDecl (L.FieldDecl _ names _) = concatMap extractName names

    extractGadtDecl (L.GadtDecl _ name _) = extractName name

    extractClassDecl (L.ClsDecl _ decl) = extract decl
    extractClassDecl (L.ClsDataFam _ _ head _) = extractDeclHead head
    extractClassDecl (L.ClsTyFam _ head _) = extractDeclHead head
    extractClassDecl _ = []

    extractName (L.Ident loc name) = [(name, getLoc loc)]
    extractName (L.Symbol _ _) = []   -- no symbols for now

localDecls _ = Map.empty

getLoc :: L.SrcSpanInfo -> Defn
getLoc (L.SrcSpanInfo (L.SrcSpan file line _ _ _) _) = Defn file line

thingMembers :: L.Module L.SrcSpanInfo -> String -> [String]
thingMembers (L.Module _ _ _ _ decls) name = concatMap extract decls
    where
    extract (L.DataDecl _ _ _ head condecls _) | nameOfHead head == Just name = concatMap getQualConDecl condecls
    extract (L.GDataDecl _ _ _ head _ condecls _) | nameOfHead head == Just name = concatMap getGadtDecl condecls
    extract (L.ClassDecl _ _ head _ (Just classdecls)) | nameOfHead head == Just name = concatMap getClassDecl classdecls
    extract _ = []

    getQualConDecl (L.QualConDecl _ _ _ (L.ConDecl _ (L.Ident _ name) _)) = [name]
    getQualConDecl (L.QualConDecl _ _ _ (L.RecDecl _ (L.Ident _ name) fields)) = name : concatMap getField fields
    getQualConDecl _ = []

    getGadtDecl (L.GadtDecl _ name _) = getName name
    
    getField (L.FieldDecl _ names _) = concatMap getName names

    getClassDecl (L.ClsDecl _ (L.FunBind _ (L.Match _ name _ _ _ : _))) = getName name
    getClassDecl (L.ClsDecl _ (L.PatBind _ (L.PVar _ name) _ _ _)) = getName name  
    getClassDecl _ = []

    getName (L.Ident _ name) = [name]
    getName _ = []

    nameOfHead (L.DHead _ (L.Ident _ name) _) = Just name
    nameOfHead (L.DHInfix _ _ (L.Ident _ name) _) = Just name
    nameOfHead (L.DHParen _ h) = nameOfHead h
    nameOfHead _ = Nothing
thingMembers _ _ = []

modExports :: Database -> String -> Map.Map String Defn
modExports db modname = 
    case Map.lookup modname db of
        Nothing -> Map.empty
        Just mod -> Map.filterWithKey (\k _ -> exported mod k) (localDecls mod)

exported :: L.Module L.SrcSpanInfo -> String -> Bool
exported mod@(L.Module _ (Just (L.ModuleHead _ _ _ (Just (L.ExportSpecList _ specs)))) _ _ _) name = any (matchesSpec name) specs
    where
    matchesSpec name (L.EVar _ (L.UnQual _ (L.Ident _ name'))) = name == name'
    matchesSpec name (L.EAbs _ (L.UnQual _ (L.Ident _ name'))) = name == name'
    matchesSpec name (L.EThingAll _ (L.UnQual _ (L.Ident _ name'))) = name == name' || (name `elem` thingMembers mod name')
    matchesSpec name (L.EThingWith _ (L.UnQual _ (L.Ident _ name')) cnames) = name == name' || any (matchesCName name) cnames
    matchesSpec _ (L.EModuleContents _ (L.ModuleName _ _)) = False  -- XXX wrong, moduleScope handles it though
    matchesSpec _ _ = False
    
    matchesCName name (L.VarName _ (L.Ident _ name')) = name == name'
    matchesCName name (L.ConName _ (L.Ident _ name')) = name == name'
    matchesCName _ _ = False
exported _ _ = True

moduleScope :: Database -> L.Module L.SrcSpanInfo -> Map.Map String Defn
moduleScope db mod@(L.Module _ modhead _ imports _) = Map.unions $ moduleItself : localDecls mod : map extractImport imports
    where

    moduleItself = moduleDecl modhead `Map.union` enclosingFilename mod

    moduleDecl (Just (L.ModuleHead l (L.ModuleName _ name) _ _)) = Map.singleton name (getLoc l)
    moduleDecl _ = Map.empty

    enclosingFilename (L.Module l _ _ _ _) = Map.singleton (filename l) (getLoc l)
    enclosingFilename _ = Map.empty

    filename (L.SrcSpanInfo (L.SrcSpan file _ _ _ _) _) = takeFileName file
    
    extractImport decl@(L.ImportDecl { L.importModule = L.ModuleName _ name, L.importSpecs = spec }) = 
        Map.unions [
            if L.importQualified decl then Map.empty else names,
            Map.mapKeys ((name ++ ".") ++) names,
            case L.importAs decl of
                Nothing -> Map.empty
                Just (L.ModuleName _ name') -> Map.mapKeys ((name' ++ ".") ++) names,
            extraExports
        ]
        
        where
        names | Just (L.ImportSpecList _ True specs) <- spec = normalExports `Map.difference` (Map.fromList (map (flip (,) ()) (concatMap specName specs)))
              | Just (L.ImportSpecList _ False specs) <- spec = Map.filterWithKey (\k _ -> k `elem` concatMap specName specs) normalExports
              | otherwise = normalExports

        normalExports = modExports db name

        specName (L.IVar _ (L.Ident _ name)) = [name]
        specName (L.IAbs _ (L.Ident _ name)) = [name]
        specName (L.IThingAll _ (L.Ident _ name)) = [name]  -- XXX incorrect, need its member names
        specName (L.IThingWith _ (L.Ident _ name) cnames) = name : concatMap cname cnames
        specName _ = []

        cname (L.VarName _ (L.Ident _ name)) = [name]
        cname (L.ConName _ (L.Ident _ name)) = [name]
        cname _ = []

    extraExports | Just (L.ModuleHead _ _ _ (Just (L.ExportSpecList _ especs))) <- modhead =
            Map.unions [ modExports db modname | L.EModuleContents _ (L.ModuleName _ modname) <- especs ]
                | otherwise = Map.empty

moduleScope _ _ = Map.empty

makeTag :: FilePath -> (String, Defn) -> String
makeTag refFile (name, Defn file line) = name ++ "\t" ++ file ++ "\t" ++ show line ++ ";\"\t" ++ "file:" ++ refFile

makeTags :: FilePath -> Map.Map String Defn -> [String]
makeTags refFile = map (makeTag refFile) . Map.assocs

haskellSource :: FilePath -> IO String
haskellSource file = do
    contents <- readFile file
    let needsCpp = maybe False (L.CPP `elem`) (L.readExtensions contents)
    if needsCpp
        then CPP.runCpphs cppOpts file contents
        else return contents
    where
    cppOpts = CPP.defaultCpphsOptions { CPP.boolopts = CPP.defaultBoolOptions { CPP.hashline = False } }
    

makeDatabase :: [FilePath] -> IO Database
makeDatabase files = do
    fmap (Map.fromList . concat) . forM files $ \file -> do
        result <- L.parseFileContentsWithMode (mode file) `fmap` haskellSource file
        case result of
            L.ParseOk mod@(L.Module _ (Just (L.ModuleHead _ (L.ModuleName _ name) _ _)) _ _ _) -> do
                return [(name, mod)]
            L.ParseFailed loc str -> do
                hPutStrLn stderr $ "Parse error: " ++  show loc ++ ": " ++ str
                return []
            _ -> do
                return []
    where
    mode filename = L.ParseMode {
        L.parseFilename = filename,
        L.extensions = [L.MultiParamTypeClasses, L.ExistentialQuantification, L.FlexibleContexts],
        L.ignoreLanguagePragmas = False,
        L.ignoreLinePragmas = False,
        L.fixities = Nothing
      }

moduleFile :: L.Module L.SrcSpanInfo -> FilePath
moduleFile (L.Module (L.SrcSpanInfo (L.SrcSpan file _ _ _ _) _) _ _ _ _) = file
moduleFile _ = error "Wtf is an XmlPage/XmlHybrid?"

data Options = Options 
 { outputFile :: Maybe FilePath
 }

defaultOptions :: Options
defaultOptions = Options
 { outputFile = Nothing
 }

options :: [OptDescr (Options -> Options)]
options = [ Option ['f'] ["file"] (ReqArg (\f opts -> opts {outputFile = Just f}) "FILE") "output tags to FILE" ]

main :: IO ()
main = do
    args <- getArgs
    let (opts', files, _) = getOpt Permute options args
    let opts = foldl (flip id) defaultOptions opts'
    when (null files) $ do
        hPutStrLn stderr $ "Usage: hothasktags [-f <output_file>] <file1> <file2> ..."
    database <- makeDatabase files  
    let tags = sort $ concatMap (\mod -> makeTags (moduleFile mod) (moduleScope database mod)) (Map.elems database)
    case outputFile opts of 
        Nothing -> mapM_ putStrLn tags
        Just f -> writeFile f (unlines tags)

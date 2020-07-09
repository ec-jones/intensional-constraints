{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

module Lib
  ( plugin,
  )
where

import BinIface
import Binary
import Constraints
import Control.Monad
import qualified Data.IntSet as I
import qualified Data.Map as M
import Data.Semigroup
import GhcPlugins
import IfaceEnv
import IfaceSyn
import InferCoreExpr
import InferM
import Scheme
import System.CPUTime
import System.Directory
import TcIface
import TcRnMonad
import ToIface
import TyCoRep

plugin :: Plugin
plugin = defaultPlugin {pluginRecompile = \_ -> return NoForceRecompile, installCoreToDos = install}
  where
    install cmd todo =
      return
        ( [ CoreDoStrictness,
            CoreDoPluginPass "Constraint Inference" (inferGuts cmd)
          ]
            ++ todo
        )

interfaceName :: ModuleName -> FilePath
interfaceName = ("interface/" ++) . moduleNameString

inferGuts :: [CommandLineOption] -> ModGuts -> CoreM ModGuts
inferGuts cmd guts@ModGuts {mg_deps = d, mg_module = m, mg_binds = p} = do
  when ("debug-core" `elem` cmd) $ pprTraceM "Core Source:" $ ppr p
  hask <- getHscEnv
  liftIO $ do
    let gbl =
          IfGblEnv
            { if_doc = text "initIfaceLoad",
              if_rec_types = Nothing
            }
    env <- -- Reload saved typeschemes
      initTcRnIf 'i' hask gbl (mkIfLclEnv m empty False) $ do
        cache <- mkNameCacheUpdater
        foldM
          ( \env (interfaceName -> m_name, _) -> do
              exists <- liftIO $ doesFileExist m_name
              if exists
                then do
                  bh <- liftIO $ readBinMem m_name
                  ictx <- liftIO $ M.fromList <$> getWithUserData cache bh
                  ctx <- mapM (mapM tcIfaceTyCon) ictx
                  return (M.union ctx env)
                else return env
          )
          M.empty
          (dep_mods d)
    t0 <- getCPUTime
    -- Infer constraints
    let !gamma = runInferM (inferProg p) m env
    t1 <- getCPUTime
    if "time" `elem` cmd
      then do
        putStrLn ("top-level defns: " ++ show (length p))
        putStrLn ("max-interface: " ++ show (foldMap (Max . I.size . boundvs) gamma))
        putStrLn ("max-constraints: " ++ show (foldMap (Max . size . constraints) gamma))
        putStrLn ("time: " ++ show (t1 - t0))
      else
        -- Display typeschemes
        mapM_
          ( \(v, ts) -> do
              putStrLn ""
              putStrLn $ showSDocUnsafe $ ppr (v, ts)
              putStrLn ""
          )
          $ M.toList gamma
    -- Save typescheme to temporary file
    exist <- doesDirectoryExist "interface"
    unless exist (createDirectory "interface")
    bh <- openBinMem (1024 * 1024)
    putWithUserData
      (const $ return ())
      bh
      (M.toList $ M.filterWithKey (\k _ -> isExternalName k) (fmap toIfaceTyCon <$> gamma))
    writeBinMem bh (interfaceName (moduleName m))
    return guts

tcIfaceTyCon :: IfaceTyCon -> IfL TyCon
tcIfaceTyCon iftc = do
  e <- tcIfaceExpr (IfaceType (IfaceTyConApp iftc IA_Nil))
  case e of
    Type (TyConApp tc _) -> return tc
    _ -> pprPanic "TyCon has been corrupted!" (ppr e)

module Lib
    ( plugin
    ) where

import Types
import GenericConGraph
import InferM
import InferCoreExpr

import Control.Monad.RWS hiding (Sum, Alt)
import qualified Data.Map as M hiding (partition, filter, drop, foldr)
import Data.List

import GhcPlugins

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }
  where
    install _ todo = return ([ CoreDoStrictness, CoreDoPluginPass "Constraint Inference" (liftIO. inferGuts)] ++ todo)

name = nameStableString . getName

inferGuts :: ModGuts -> IO ModGuts
inferGuts guts@ModGuts{mg_binds = bs, mg_tcs = tcs, mg_module = m} =
    if moduleNameString (moduleName m) `elem` ["Test"]
      then do
        let env = Context{con = listToUFM (foldr buildContext [] tcs), var = M.empty}
        let p = filter (all isOfMain . bindersOf) bs
        -- Reorder p with dependencies
        -- pprTraceM "" (ppr p)
        let ((ts, _), _, _) = runRWS (listen $ inferProg p) env 0
        mapM_ (\(t, Forall as xs cs u) -> do
          putStr (show t ++ "::")
          putStrLn $ disp as xs cs u
          putStrLn "") ts
        return guts
      else
        return guts
  where
    -- Generalise this to check module name and filter type/module constructors
    isOfMain b = "$main$Test$" `isPrefixOf` name b

-- Add tycon to underlying delta (polarisation is implicit)
buildContext :: TyCon -> [(DataCon, (TyCon, [Var], [Sort]))] -> [(DataCon, (TyCon, [Var], [Sort]))]
buildContext t xs = xs' ++ xs
  where
    xs' = foldr go [] (tyConDataCons t)

    go :: DataCon -> [(DataCon, (TyCon, [Var], [Sort]))] -> [(DataCon, (TyCon, [Var], [Sort]))]
    go d ys = (d, (t, as, sorts)):ys
      where
        sorts = toSort <$> dataConOrigArgTys d
        as = dataConUnivTyVars d --Assume no existential vars

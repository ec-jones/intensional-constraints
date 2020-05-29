{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module InferM
  ( InferM,
    Error,
    InferEnv (..),
    InferState (..),
    Context,
    mkSet,
    mkCon,
    fresh,
    branch,
    branch',
    isBranchReachable,
    topLevel,
    putVar,
    putVars,
    emit,
    setLoc,
    saturate,
    runInferM,
  )
where

import Constraints
import Control.Monad.Except hiding (guard)
import Control.Monad.RWS hiding ((<>), guard)
import qualified Data.HashMap.Lazy as H
import qualified Data.IntMap as I
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import DataTypes
import Family
import GhcPlugins hiding (L, Type, empty)
import Scheme
import Types
import Prelude hiding ((<>))

data Error
  = forall l r.
    SrcError
      { collision :: SrcSpan,
        constraint :: Constraint l r
      }

instance Outputable Error where
  ppr SrcError {collision = c, constraint = a} =
    let l = left a
        r = right a
     in text "The constructor: " <> ppr l <> text ", arising at: " <> ppr (constraintLoc l)
          <> text ", can colide with the pattern: "
          <> ppr r
          <> text ", arising at: "
          <> ppr (constraintLoc r)
          <> text ", when in the function: "
          <> ppr c

-- The inference monad
type InferM = RWS InferEnv [Error] InferState

data InferEnv
  = InferEnv
      { unrollDataTypes :: Bool,
        allowContra :: Bool,
        modName :: Module,
        branchPath :: Path,
        branchGuard :: Family,
        varEnv :: Context,
        inferLoc :: SrcSpan
      }

data InferState
  = InferState
      { freshRVar :: RVar,
        congraph :: Family,
        -- Binary decision diagram state
        -- memo :: H.HashMap Memo Family,
        freshId :: ID,
        nodes :: I.IntMap Node,
        hashes :: H.HashMap Node ID
      }

instance Outputable InferState where
  ppr state = text "Nodes: " <> vcat (fmap ppr $ I.toList (nodes state))

instance GsM InferM where
  getNode i =
    gets (I.lookup i . nodes) >>= \case
      Nothing -> error ("No node with that ID!" ++ show i)
      Just n -> return n

  -- TODO: make empty typ empty
  fromNode n =
    gets (H.lookup n . hashes) >>= \case
      Nothing -> do
        s@InferState {nodes = ns, hashes = hs, freshId = i} <- get
        put
          s
            { freshId = i + 1,
              nodes = I.insert i n ns,
              hashes = H.insert n i hs
            }
        return $ ID i
      Just i -> return $ ID i

--  memo op a =
--    gets (H.lookup op . InferM.memo) >>= \case
--     Nothing -> do
--       r <- a
--       modify (\s -> s {InferM.memo = H.insert op r (InferM.memo s)})
--       return r
--     Just r -> return r

-- A fresh refinement variable
fresh :: InferM RVar
fresh = do
  s@InferState {freshRVar = i} <- get
  put s {freshRVar = i + 1}
  return i

-- Make constructors tagged by the current location
mkCon :: DataCon -> InferM (K 'L)
mkCon k = do
  l <- asks inferLoc
  return (Con (getName k) l)

mkSet :: [DataCon] -> InferM (K 'R)
mkSet ks = do
  l <- asks inferLoc
  return (Set (mkUniqSet (getName <$> ks)) l)

-- The environment variables and their types
type Context = M.Map Name Scheme

instance GsM m => Refined Context m where
  domain = foldM (\k -> fmap (L.union k) . domain) []
  rename x = mapM . rename x

-- Insert variables into environment
putVar :: Name -> Scheme -> InferM a -> InferM a
putVar n s = local (\env -> env {varEnv = M.insert n s (varEnv env)})

putVars :: Context -> InferM a -> InferM a
putVars ctx = local (\env -> env {varEnv = M.union ctx (varEnv env)})

-- A Path records the terms that have been matched against in the current path
type Path = [(CoreExpr, [Name])]

-- Check if an expression is in the path
topLevel :: CoreExpr -> InferM Bool
topLevel e = asks (foldr (\(e', _) es -> not (cheapEqExpr e e') && es) True . branchPath)

-- Check if a branch is possible, i.e. doesn't contradict the current branch
isBranchReachable :: CoreExpr -> DataCon -> InferM Bool
isBranchReachable e (getName -> k) = asks (foldr (\(e', ks) es -> (not (cheapEqExpr e e') || k `elem` ks) && es) True . branchPath)

-- Locally guard constraints and add expression to path
branch :: CoreExpr -> [DataCon] -> RVar -> DataType TyCon -> InferM a -> InferM a
branch e ks x d m
  | full (getName <$> ks) (orig d) = m
  | otherwise = do
    curr_guard <- asks branchGuard
    s <- mkSet ks
    case toAtomic s (Dom x) (getName <$> d) of
      Nothing -> error "Error in creating guard"
      Just cs -> do
        new_guard <- foldM (\a c -> insert c Empty a) curr_guard cs 
        local
          ( \env ->
              env
                { branchGuard = new_guard,
                  branchPath = (e, getName <$> ks) : branchPath env
                }
          )
          m

-- Locally guard constraints without an associated core expression
branch' :: [DataCon] -> RVar -> DataType TyCon -> InferM a -> InferM a
branch' ks x d m
  | full (getName <$> ks) (orig d) = m
  | otherwise = do
    curr_guard <- asks branchGuard
    s <- mkSet ks
    case toAtomic s (Dom x) (getName <$> d) of
      Nothing -> error "Error in creating guard"
      Just cs -> do
        new_guard <- foldM (\a c -> insert c Empty a) curr_guard cs 
        local
          ( \env ->
              env
                { branchGuard = new_guard
                }
          )
          m

setLoc :: RealSrcSpan -> InferM a -> InferM a
setLoc l = local (\env -> env {inferLoc = RealSrcSpan l})

emit :: K l -> K r -> DataType TyCon -> InferM ()
emit k1 k2 d
  | not (trivial (orig d) || full (cons k2) (orig d)) =
    case toAtomic k1 k2 (getName <$> d) of
      Nothing -> do
        l <- asks inferLoc
        tell [SrcError l (Constraint k1 k2 (fmap getName d))]
      Just cs -> do
        cg <- gets congraph
        g <- asks branchGuard
        cg' <- foldM (\cg' a -> insert a g cg') cg cs
        modify (\s -> s {congraph = cg'})
  | otherwise = return ()

full :: [Name] -> TyCon -> Bool
full ks d = ks == fmap getName (tyConDataCons d)

runInferM ::
  InferM a ->
  Bool ->
  Bool ->
  Module ->
  M.Map Name Scheme ->
  (a, InferState, [Error])
runInferM run unroll allow_contra mod_name init_env =
  runRWS
    (
        local (\e -> e {varEnv = init_env}) run
    )
    (InferEnv unroll allow_contra mod_name [] Empty M.empty (UnhelpfulSpan (mkFastString "Top level")))
    (InferState 0 Empty 0 I.empty H.empty)

-- Transitively remove local constraints and attach them to variables
saturate :: Context -> InferM Context
saturate ts = do
  interface <- domain ts
  cg <- gets congraph >>= restrict interface
  modify (\s -> s {- InferM.memo = H.empty, -} {hashes = H.empty, congraph = Empty})
  l <- asks inferLoc
  tell [SrcError {collision = l, constraint = e} | e <- getErrors cg]
  return ((\s -> s {boundvs = interface, constraints = Just cg}) <$> ts)

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}

module Tree
  ( CsM (..),
    Constraints (Empty, Errors),
    Memo,
    ID,
    Node,
    insert,
    guardWith,
    union,
    trans,
    toList,
    fromList,
  )
where

import Constraints
import Control.Monad.State
import Data.Hashable
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import DataTypes
import GHC.Generics
import GhcPlugins (Name)
import Types
import Prelude hiding ((<>), or)

-- A GuardState monad contins a directed acyclic graph of nodes
class MonadState state m => CsM state s m | m -> state, state -> s where
  lookupNode :: ID -> m (Node s)
  lookupHash :: Node s -> m (Maybe ID)
  freshNode :: Node s -> m ID

  -- Only run an operation if its new
  memo :: Memo s -> m (Constraints s) -> m (Constraints s)

-- An internal node with a unique ID
type ID = Int

-- Operation DSL
data Memo s
  = Union !ID !ID
  | Or !ID !ID
  | GuardWith !ID !ID
  deriving (Eq, Ord, Generic)

instance Hashable (Memo s)

data Node s
  = Node
      { atom :: Atomic,
        lo, hi :: Constraints s
      }
  deriving (Eq, Generic)

instance Hashable (Node s)

-- A stateful set of possible constraint sets
data Constraints s
  = Empty -- The empty constraint set
  | Errors [Atomic] -- An unsatisfiable branch
  | ID ID
  deriving (Eq, Ord, Generic)

pattern Bot :: Constraints s
pattern Bot = Errors []

instance Hashable (Constraints s)

instance CsM state s m => Refined (Constraints s) m where
  domain (ID i) = do
    n <- lookupNode i
    da <- domain (atom n)
    dl <- domain (lo n)
    dh <- domain (hi n)
    return (da `L.union` dl `L.union` dh)
  domain _ = return []

  renameAll xys (ID i) = do
    n <- lookupNode i
    a <- renameAll xys (atom n)
    lo' <- renameAll xys (lo n)
    hi' <- renameAll xys (hi n)
    mkSet $ Node a lo' hi'
  renameAll _ p = return p

-- Make a new constraint from a node (or reuse an existing node)
mkSet :: CsM state s m => Node s -> m (Constraints s)
mkSet n
  | hi n == lo n = return (hi n) -- Skip redundant nodes
  | otherwise =
    lookupHash n >>= \case
      Just j -> return (ID j) -- Node sharing
      Nothing -> ID <$> freshNode n

-- Insert an atomic constraint guarded by a constraint set
insert :: CsM state s m => Atomic -> Constraints s -> Constraints s -> m (Constraints s)
insert a p q = mkSet (Node a Bot Empty) >>= guardWith p >>= union q

guardWith :: CsM state s m => Constraints s -> Constraints s -> m (Constraints s)
guardWith Empty p = return p
guardWith (Errors _) _ = return Empty
guardWith _ Empty = return Empty
guardWith (ID i) (Errors a) = do
  n <- lookupNode i
  lo' <- guardWith (lo n) (Errors a)
  hi' <- guardWith (hi n) (Errors a)
  mkSet $ Node (atom n) lo' hi'
guardWith p@(ID i) q@(ID j) =
  memo (GuardWith i j) $ do
    n <- lookupNode i
    m <- lookupNode j
    case compare (atom n) (atom m) of
      LT -> do
        lo' <- lo n `guardWith` q
        hi' <- hi n `guardWith` q
        mkSet $ Node (atom n) lo' hi'
      EQ -> do
        lo' <- lo n `guardWith` lo m
        hi' <- hi n `guardWith` hi m
        mkSet $ Node (atom n) lo' hi'
      GT -> do
        lo' <- p `guardWith` lo m
        hi' <- p `guardWith` hi m
        mkSet $ Node (atom m) lo' hi'

-- Combine two constraint sets; decreases the model space
union :: CsM state s m => Constraints s -> Constraints s -> m (Constraints s)
union p q | p == q = return p
union (Errors a) (Errors b) = return (Errors (a ++ b))
union (Errors a) _ = return (Errors a)
union _ (Errors a) = return (Errors a)
union Empty q = return q
union p Empty = return p
union p@(ID i) q@(ID j) =
  memo (Union (min i j) (max i j)) $ do
    n <- lookupNode i
    m <- lookupNode j
    case compare (atom n) (atom m) of
      LT -> do
        lo' <- lo n `union` q
        hi' <- hi n `union` q
        mkSet $ Node (atom n) lo' hi'
      EQ -> do
        lo' <- lo n `union` lo m
        hi' <- hi n `union` hi m
        mkSet $ Node (atom n) lo' hi'
      GT -> do
        lo' <- p `union` lo m
        hi' <- p `union` hi m
        mkSet $ Node (atom m) lo' hi'

-- Take the disjunction of two alternative constraint sets; increases the model space
or :: CsM state s m => Constraints s -> Constraints s -> m (Constraints s)
or p q | p == q = return p
or Empty _ = return Empty
or _ Empty = return Empty
or (Errors _) p = return p
or q (Errors _) = return q
or p@(ID i) q@(ID j) =
  memo (Or (min i j) (max i j)) $ do
    n <- lookupNode i
    m <- lookupNode j
    case compare (atom n) (atom m) of
      LT -> do
        lo' <- lo n `or` q
        hi' <- hi n `or` q
        mkSet $ Node (atom n) lo' hi'
      EQ -> do
        lo' <- lo n `or` lo m
        hi' <- hi n `or` hi m
        mkSet $ Node (atom n) lo' hi'
      GT -> do
        lo' <- p `or` lo m
        hi' <- p `or` hi m
        mkSet $ Node (atom m) lo' hi'

type AdjMap = M.Map (DataType Name) (M.Map (K 'L) (S.Set (K 'R)))

-- Add an edge, and any transitive edges, to the adjacency map
insertEdge :: Atomic -> AdjMap -> Either [Atomic] AdjMap
insertEdge a adj
  | safe (left a) (right a) = do
    ps <- preds
    ss <- succs
    return
      ( M.alter
          (Just . M.insertWith S.union (left a) ss . fromMaybe M.empty)
          (dataty a)
          ps
      )
  | otherwise = Left [a]
  where
    succs =
      case right a of
        Dom y ->
          case M.lookup (dataty a) adj >>= M.lookup (Dom y) of
            Nothing -> return (S.singleton (right a))
            Just rs -> do
              let unsafe = S.filter (not . safe (left a)) rs
              if S.null unsafe
                then return (S.insert (right a) rs)
                else Left (S.foldr (\r -> L.insert (Constraint (left a) r (dataty a))) [] unsafe)
        _ -> return (S.singleton (right a))
    preds =
      case left a of
        Dom x ->
          M.traverseWithKey
            ( \d ->
                M.traverseWithKey
                  ( \l rs ->
                      if S.member (Dom x) rs
                        then
                          if safe l (Dom x)
                            then return (S.insert (right a) rs)
                            else Left [Constraint l (Dom x) d]
                        else return rs
                  )
            )
            adj
        _ -> return adj

-- Does an adjacency map contain an edge
memberEdge :: Atomic -> AdjMap -> Bool
memberEdge a adj =
  case M.lookup (dataty a) adj >>= M.lookup (left a) of
    Nothing -> False
    Just rs -> S.member (right a) rs

-- Take the transitive closure of the decision tree with initial adjacency map and set of interface nodes
trans :: CsM state s m => AdjMap -> [RVar] -> Constraints s -> m (Constraints s)
trans _ _ Empty = return Empty
trans _ _ (Errors a) = return (Errors a)
trans adj xs (ID i) = do
  n <- lookupNode i
  if  -- If edge is already satisfied
      | memberEdge (atom n) adj -> trans adj xs (hi n)
      -- Interface edges that are unsatisfied
      | interface (left (atom n)) && interface (right (atom n)) -> do
        lo' <- trans adj xs (lo n)
        case insertEdge (atom n) adj of
          Left es ->
            mkSet $ Node (atom n) lo' (Errors es) -- Conditional errors
          Right adj' -> do
            hi' <- trans adj' xs (hi n)
            mkSet $ Node (atom n) lo' hi'
      -- Intermediate edges that are unsatisfied
      | otherwise -> trans adj xs (lo n)
  where
    interface (Dom x) = x `elem` xs
    interface _ = True

-- Convert to DNF
toList :: CsM state s m => Constraints s -> m [[Atomic]]
toList Empty = return [[]]
toList (Errors _) = return []
toList (ID i) = do
  n <- lookupNode i
  hi' <- toList (hi n)
  lo' <- toList (lo n)
  return ([atom n : as | as <- hi'] ++ lo')

-- Convert from DNF
fromList :: CsM state s m => [[Atomic]] -> m (Constraints s)
fromList =
  foldM
    ( \cs as ->
        foldM (\as' a -> insert a Empty as') Empty as >>= or cs
    )
    Bot

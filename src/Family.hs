{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}

module Family
  ( Family (..),
    AdjMap,
    ID,
    Node (..),
    GsM (..),
    addEdge,
    insert,
    union,
    guardWith,
    restrict,
  )
where

import Constraints
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Hashable
import qualified Data.List as L
import DataTypes
import GHC.Generics
import GhcPlugins hiding (L, empty, isEmpty, singleton)
import Types

-- An unlabelled directed graph
type AdjMap = HM.HashMap (DataType Name) (HM.HashMap (K 'L) (HS.HashSet (K 'R)))

instance Outputable AdjMap where
  ppr m =
    vcat
      [ pprCon k1 d <+> arrowt <+> pprCon k2 d
        | (d, sg) <- HM.toList m,
          (k1, to) <- HM.toList sg,
          k2 <- HS.toList to
      ]
    where
      pprCon k@(Dom _) d = ppr d GhcPlugins.<> parens (ppr k)
      pprCon k _ = ppr k

instance Monad m => Refined Name m where
  domain _ = return []
  rename _ _ = return

instance (Eq a, Hashable a, Refined a m) => Refined (HS.HashSet a) m where
  domain = foldM (\a -> fmap (L.union a) . domain) []
  rename x y m = HS.fromList <$> (mapM (rename x y) $ HS.toList m)

instance (Eq k, Hashable k, Refined k m, Refined a m) => Refined (HM.HashMap k a) m where
  domain m =
    liftM2
      L.union
      (foldM (\l -> fmap (L.union l) . domain) [] $ HM.keys m)
      (foldM (\l -> fmap (L.union l) . domain) [] m)
  rename x y m = HM.fromList <$> (mapM ((\(l, r) -> (,) <$> rename x y l <*> rename x y r)) $ HM.toList m)

-- Check if an edge is in the graph
hasEdge :: Atomic -> AdjMap -> Bool
hasEdge a g =
  case HM.lookup (dataty a) g >>= HM.lookup (left a) of
    Nothing -> False
    Just rs -> HS.member (right a) rs

-- Add a new edge to a graph
addEdge :: Atomic -> AdjMap -> AdjMap
addEdge a = HM.insertWith (HM.unionWith HS.union) (dataty a) $ HM.singleton (left a) $ HS.singleton (right a)

singleton :: Atomic -> AdjMap
singleton a = addEdge a HM.empty

-- Overlay graphs
overlay :: AdjMap -> AdjMap -> AdjMap
overlay = HM.unionWith (HM.unionWith HS.union)

-- The relative complement of graphs
difference :: AdjMap -> AdjMap -> AdjMap
difference = HM.differenceWith (\sg -> Just . HM.differenceWith (\rs -> Just . HS.difference rs) sg)

intersect :: AdjMap -> AdjMap -> Maybe AdjMap
intersect l r = chkEmpty $ HM.intersectionWith (HM.intersectionWith HS.intersection) l r
  where
    chkEmpty m
      | null m = Nothing
      | all null m = Nothing
      | all (all null) m = Nothing
      | otherwise = Just m

-- Restrict a graph to only nodes from a certain set
restrictGraph :: [RVar] -> AdjMap -> AdjMap
restrictGraph xs = fmap (HM.foldrWithKey go HM.empty)
  where
    go l rs sg
      | interface l = HM.insertWith HS.union l (HS.filter interface rs) sg
      | otherwise = sg
    interface (Dom x) = x `elem` xs
    interface _ = True

-- Accumalate errors from a graph
unsafeEdges :: AdjMap -> Maybe [Atomic]
unsafeEdges = HM.foldrWithKey (\d m k -> HM.foldrWithKey (\x -> mappend . foldMap (unsafeEdge d x)) k m) Nothing
  where
    unsafeEdge d l r
      | safe l r = Nothing
      | otherwise = Just [Constraint l r d]

hasUnsafeEdges :: AdjMap -> Bool
hasUnsafeEdges = getAny . foldMap (HM.foldrWithKey (\x -> mappend . foldMap (Any . not . safe x)) mempty)

-- Take the transitive closure of a graph from a specified frontier
trans :: AdjMap -> HS.HashSet (K 'L) -> AdjMap
trans g s = HM.mapWithKey (\d dm -> evalState (foldM (go d) dm s) HS.empty) g
  where
    go :: DataType Name -> HM.HashMap (K 'L) (HS.HashSet (K 'R)) -> K 'L -> State (HS.HashSet (K 'L)) (HM.HashMap (K 'L) (HS.HashSet (K 'R)))
    go d sg l =
      gets (HS.member l) >>= \case
        True -> return sg -- Skip explored nodes
        False -> do
          modify (HS.insert l) -- Add x to the set of explored nodes
          case HM.lookup d g >>= HM.lookup l of -- Lookup edges from the original map
            Nothing -> return sg
            Just rs ->
              foldM
                ( \sg' -> \case
                    Dom x -> do
                      sg'' <- go d sg' (Dom x) -- Process successor
                      case HM.lookup (Dom x) sg'' of
                        Nothing -> return sg''
                        Just rs' -> return (HM.insertWith HS.union l rs' sg'') -- Add transitive edges
                    _ -> return sg'
                )
                sg
                rs

-- A family of graphs
data Family
  = ID ID
  | Empty
  | Error [Atomic]
  deriving (Eq, Generic)

instance Hashable Family

instance Outputable Family where
  ppr (ID i) = ppr i
  ppr Empty = text "Empty"
  ppr (Error as) = ppr as

instance GsM m => Refined Family m where
  domain (ID i) =
    getNode i >>= \case
      Node a ds -> do
        da <- foldM (\l -> fmap (L.union l) . domain) [] a
        foldM (\l -> fmap (L.union l) . domain) da ds
  domain (Error e) = foldM (\l -> fmap (L.union l) . domain) [] e
  domain Empty = return []

  rename x y (ID i) =
    getNode i >>= \case
      Node a ds -> do
        a' <- mapM (rename x y) a
        ds' <- mapM (rename x y) ds
        fromNode $ Node a' ds'
  rename x y (Error as) = Error <$> mapM (rename x y) as
  rename _ _ Empty = return Empty

type ID = Int

-- No delta map leads to an empty tip
data Node
  = Node AdjMap (HM.HashMap AdjMap Family)
  deriving (Eq, Generic)

instance Outputable Node where
  ppr (Node a ds) = text "Delta: " <+> ppr a <+> vcat (ppr <$> HM.toList ds)

instance Hashable Node

-- A graph state monad contins a directed acyclic graph of nodes
-- TODO: Memoization
class Monad m => GsM m where
  getNode :: ID -> m Node
  fromNode :: Node -> m Family

insert :: GsM m => Atomic -> AdjMap -> Family -> m Family
insert a g f -- Skip tautologies
  | hasEdge a g || hasUnsafeEdges g = return f
insert a _ (Error es)
  | safe (left a) (right a) = return $ Error es
  | otherwise = return $ Error (a : es)
insert a g Empty = do
  t <- fromNode $ Node (singleton a) HM.empty
  fromNode $ Node HM.empty $ HM.singleton g t
insert a g f@(ID i) = do
  Node t ds <- getNode i
  if hasEdge a t
    then return f
    else do
      let g' = difference g t
      (ds', Any found) <-
        runWriterT
          ( mapM
              (go g')
              (HM.toList ds)
          )
      if found
        then fromNode $ Node t $ HM.fromList ds'
        else do
          -- If g' is disjoint from all existing branches
          t' <- fromNode $ Node (singleton a) HM.empty
          fromNode $ Node t $ HM.insert g' t' ds
  where
    -- Rebuild with common prefixes
    go :: GsM m => AdjMap -> (AdjMap, Family) -> WriterT Any m (AdjMap, Family)
    go g' (delta, f) =
      case g' `intersect` delta of
        Nothing -> return (delta, f)
        Just ig -> do
          tell (Any True)
          f' <- lift $ insert a (difference g' ig) f
          return (ig, f')

-- Iteratively insert every edge in an adjacency map
insertMany :: GsM m => AdjMap -> AdjMap -> Family -> m Family
insertMany as g f =
  HM.foldrWithKey
    ( \d dm mf ->
        HM.foldrWithKey
          ( \l lm mf ->
              foldr
                ( \r mf ->
                    mf >>= insert (Constraint l r d) g
                )
                mf
                lm
          )
          mf
          dm
    )
    (return f)
    as

-- Union of constriant sets from two families
union :: GsM m => Family -> Family -> m Family
union (Error es) (Error es') = return (Error (es ++ es'))
union (Error es) _ = return (Error es)
union Empty f = return f
union f f' = go HM.empty f (return f')
  where
    go _ (Error es) mf =
      mf >>= \case
        Error es' -> return (Error (es ++ es')) -- Add errors to mf
        _ -> return (Error es)
    go _ Empty mf = mf
    go delta (ID j) mf = do
      f <- mf
      Node t ds <- getNode j
      HM.foldrWithKey
        go
        (insertMany t delta f)
        ds

-- Make a family that is conditional on another family
guardWith :: GsM m => Family -> AdjMap -> m Family
guardWith Empty _ = return Empty
guardWith (Error es) _ = return (Error es)
guardWith (ID i) g = do
  Node t ds <- getNode i
  HM.foldrWithKey
    ( \delta k mf -> do
        f <- mf
        k' <- guardWith k (overlay g delta)
        union f k'
    )
    (insertMany t g Empty)
    ds

-- Remove a set of nodes adding any transitive edges
restrict :: GsM m => [RVar] -> Family -> m Family
restrict s = go HM.empty
  where
    transWith :: AdjMap -> AdjMap -> AdjMap
    transWith x g = trans (overlay x g) $ foldMap HM.keysSet g
    go :: GsM m => AdjMap -> Family -> m Family
    go _ Empty = return Empty
    go _ (Error e) = return $ Error e
    go x (ID i) = do
      Node t ds <- getNode i
      let t' = transWith x t
      case unsafeEdges t' of
        Just e -> return $ Error e
        Nothing ->
          HM.foldrWithKey
            ( \delta k acc -> do
                let y = transWith x delta
                case unsafeEdges y of
                  Just _ -> acc
                  Nothing -> do
                    k' <- go y k
                    k'' <- guardWith k' (restrictGraph s y)
                    acc >>= union k''
            )
            (fromNode $ Node (restrictGraph s t') HM.empty)
            ds

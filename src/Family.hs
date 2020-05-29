{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Family
  ( Family (..),
    ID,
    Node (..),
    GsM (..),
    empty,
    getErrors,
    insert,
    union,
    guardWith,
    restrict,
  )
where

import Constraints
import Control.Monad.State
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Hashable
import qualified Data.List as L
import DataTypes
import GHC.Generics
import GhcPlugins hiding (L, empty, isEmpty, singleton)
import Types
import Prelude hiding ((<>))

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
      pprCon k@(Dom _) d = ppr d <> parens (ppr k)
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

commonSubgraph :: AdjMap -> AdjMap -> Maybe AdjMap
commonSubgraph = undefined

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
graphErrors :: AdjMap -> Maybe [Atomic]
graphErrors = HM.foldrWithKey (\d m k -> HM.foldrWithKey (\x -> mappend . foldMap (unsafeEdge d x)) k m) Nothing
  where
    unsafeEdge d l r
      | safe l r = Nothing
      | otherwise = Just [Constraint l r d]

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
      Tip a -> foldM (\l -> fmap (L.union l) . domain) [] a
      Delta ds -> foldM (\l -> fmap (L.union l) . domain) [] ds
  domain (Error e) = foldM (\l -> fmap (L.union l) . domain) [] e
  domain Empty = return []

  rename x y (ID i) =
    getNode i >>= \case
      Tip a -> mapM (rename x y) a >>= fromNode . Tip
      Delta ds -> mapM (rename x y) ds >>= fromNode . Delta
  rename x y (Error as) = Error <$> mapM (rename x y) as
  rename _ _ Empty = return Empty

type ID = Int

-- No delta map leads to an empty tip
-- Each key of the delta map is disjoint
data Node
  = Tip AdjMap
  | Delta (HM.HashMap AdjMap Family)
  deriving (Eq, Generic)

instance Outputable Node where
  ppr (Tip a) = text "Tip: " <+> ppr a
  ppr (Delta a) = text "Delta: " <+> vcat (ppr <$> HM.toList a)

instance Hashable Node

-- A graph state monad contins a directed acyclic graph of nodes
-- TODO: Memoization
class Monad m => GsM m where
  getNode :: ID -> m Node
  fromNode :: Node -> m Family

empty :: GsM m => m Family
empty = fromNode $ Tip HM.empty

getErrors :: Family -> [Atomic]
getErrors (Error e) = e
getErrors _ = []

-- Is the family trivially satisfied
isEmpty :: GsM m => Family -> m Bool
isEmpty Empty = return True
isEmpty (Error _) = return False
isEmpty (ID i) =
  getNode i >>= \case
    Tip g -> return (not $ HM.null g)
    Delta _ -> return False

-- Add a new delta, merging any common branches
insertDeltas :: GsM m => AdjMap -> Family -> HM.HashMap AdjMap Family -> m (HM.HashMap AdjMap Family)
insertDeltas delta k m =
  case HM.traverseWithKey
    ( \delta' k' ->
        case commonSubgraph delta delta' of
          Nothing -> Right k'
          -- extract the first key that matches
          -- ! Assumes the original delta map satisfies the invariants
          Just delta'' -> Left (delta', delta'', k')
    )
    m of
    Left (_, _, Empty) -> error "Delta map should not point to an empty tip!"
    Left (delta', _, e@(Error _)) -> do
      e' <- union e k -- Combine errors
      return (HM.insert delta' e' m)
    Left (delta', delta'', ID i) ->
      getNode i >>= \case
        Delta m' -> do
          k' <- remove k delta'
          m'' <-
            insertDeltas delta'' k' m'
              >>= fromNode . Delta
          return (HM.insert delta' m'' m)
        Tip g -> do
          g' <-
            fromNode (Tip $ difference g delta'')
              >>= fromNode . Delta . HM.singleton delta''
          return (HM.insert delta' g' m)
    Right _ -> return (HM.insert delta k m)

-- Insert an edge into graph in the family
insertUnguarded :: GsM m => Atomic -> Family -> m Family
insertUnguarded a Empty = fromNode (Tip $ addEdge a HM.empty)
insertUnguarded _ (Error e) = return (Error e)
insertUnguarded a (ID i) =
  getNode i >>= \case
    Tip g -> fromNode (Tip $ addEdge a g)
    Delta ds ->
      insertDeltas (singleton a) Empty ds
        >>= fromNode . Delta

insert :: GsM m => Atomic -> Family -> Family -> m Family
insert a g f =
  insertUnguarded a Empty >>= guardWith g >>= union f

-- Remove a subgraph from every graph in the family
remove :: GsM m => Family -> AdjMap -> m Family
remove Empty _ = return Empty
remove (Error e) _ = return (Error e)
remove (ID i) g =
  getNode i >>= \case
    Tip g' -> fromNode (Tip $ difference g' g)
    Delta ds ->
      HM.foldrWithKey go (return HM.empty) ds
        >>= fromNode . Delta
  where
    go delta k acc = do
      k' <- remove k g
      isEmpty k' >>= \case
        True -> acc -- Remove trivially satisfied subgraphs, i.e. empty tips
        False ->
          acc >>= insertDeltas (difference delta g) k'

-- Every combination of overlayed grgaphs
union :: GsM m => Family -> Family -> m Family
union Empty x = return x
union x Empty = return x
union (Error e) (Error e') = return (Error (mappend e e'))
union (Error e) _ = return (Error e)
union _ (Error e) = return (Error e)
union x@(ID i) y@(ID j) =
  getNode i >>= \case
    Delta ds ->
      HM.traverseWithKey (\d k -> remove y d >>= union k) ds
        >>= fromNode . Delta
    Tip g ->
      getNode j >>= \case
        Tip g' -> fromNode (Tip $ overlay g g')
        Delta ds ->
          HM.traverseWithKey (\d k -> remove x d >>= union k) ds
            >>= fromNode . Delta

-- Make a family that is conditional on another family
guardWith :: GsM m => Family -> Family -> m Family
guardWith Empty x = return x
guardWith (Error _) _ = empty
guardWith (ID i) x =
  getNode i >>= \case
    Delta ds ->
      HM.traverseWithKey (\d k -> remove x d >>= guardWith k) ds
        >>= fromNode . Delta
    Tip g ->
      remove x g >>= fromNode . Delta . HM.singleton g

-- Remove a set of nodes adding any transitive edges
restrict :: GsM m => [RVar] -> Family -> m Family
restrict s = go HM.empty
  where
    transWith :: AdjMap -> AdjMap -> AdjMap
    transWith x g = trans (overlay x g) $ foldMap HM.keysSet g
    go :: GsM m => AdjMap -> Family -> m Family
    go _ Empty = return Empty
    go _ (Error e) = return $ Error e
    go x (ID i) =
      getNode i >>= \case
        Tip g -> do
          let y = transWith x g
          case graphErrors y of
            Nothing -> fromNode $ Tip $ difference (restrictGraph s y) x
            Just e -> return $ Error e
        Delta ds ->
          HM.foldrWithKey
            ( \delta k acc -> do
                let y = transWith x delta
                case graphErrors y of
                  Just _ -> acc
                  Nothing -> do
                    k' <- go y k
                    acc >>= insertDeltas (difference (restrictGraph s y) x) k'
            )
            (return HM.empty)
            ds
            >>= fromNode . Delta

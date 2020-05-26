{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Constraints
  ( Side (..),
    K (..),
    Atomic,
    Constraint (..),
    safe,
    toAtomic,
    constraintLoc,
    cons,
  )
where

import Binary
import Data.Hashable
import qualified Data.List as L
import DataTypes
import GHC.Generics
import GhcPlugins hiding (L)
import Types
import Unique
import Prelude hiding ((<>))

data Side = L | R

-- An atomic constructor set with a location tag
data K (s :: Side) where
  Con :: Name -> SrcSpan -> K 'L
  Dom :: RVar -> K s
  Set :: UniqSet Name -> SrcSpan -> K 'R

type Atomic = Constraint 'L 'R

data Constraint l r
  = Constraint
      { left :: K l,
        right :: K r,
        dataty :: DataType Name
      }
  deriving (Eq, Ord, Generic)

instance Hashable (Constraint l r)

instance (Binary (K l), Binary (K r)) => Binary (Constraint l r) where
  get bh = do
    l <- get bh
    r <- get bh
    d <- get bh
    return (Constraint l r d)

  put_ bh (Constraint l r d) = put_ bh l >> put_ bh r >> put_ bh d

instance Outputable (Constraint l r) where
  ppr (Constraint l r d) = pprCon l <+> arrowt <+> pprCon r
    where
      pprCon :: K l -> SDoc
      pprCon k@(Dom _) = ppr d <> parens (ppr k)
      pprCon k = ppr k

instance Monad m => Refined (Constraint l r) m where
  domain (Constraint l r _) = L.union <$> domain l <*> domain r

  rename x y (Constraint l r d) = Constraint <$> rename x y l <*> rename x y r <*> pure d

-- Disregard location in comparison
instance Eq (K s) where
  Dom x == Dom x' = x == x'
  Set s _ == Set s' _ = s == s'
  Con k _ == Con k' _ = k == k'
  _ == _ = False

instance Ord (K s) where
  Con a _ <= Con b _ = a <= b
  Con _ _ <= _ = True
  Dom x <= Dom y = x <= y
  Dom _ <= _ = True
  Set as _ <= Set bs _ = nonDetEltsUniqSet as <= nonDetEltsUniqSet bs
  _ <= _ = False

instance Hashable Unique where
  hashWithSalt s = hashWithSalt s . getKey

instance Hashable Name where
  hashWithSalt s = hashWithSalt s . getUnique

instance Hashable (K s) where
  hashWithSalt s (Dom x) = hashWithSalt s x
  hashWithSalt s (Set n _) = hashWithSalt s $ nonDetKeysUniqSet n
  hashWithSalt s (Con n _) = hashWithSalt s $ getUnique n

instance Outputable (K s) where
  ppr (Dom x) = text "dom" <> parens (ppr x)
  ppr (Con k _) = ppr k
  ppr (Set ks _)
    | isEmptyUniqSet ks = unicodeSyntax (char '∅') (ppr "{}")
    | otherwise = pprWithBars ppr (nonDetEltsUniqSet ks)

instance Binary (K 'L) where
  put_ bh (Dom x) = put_ bh True >> put_ bh x
  put_ bh (Con k l) = put_ bh False >> put_ bh k >> put_ bh l

  get bh = do
    n <- get bh
    if n
      then do
        x <- get bh
        return (Dom x)
      else do
        k <- get bh
        l <- get bh
        return (Con k l)

instance Binary (K 'R) where
  put_ bh (Dom x) = put_ bh True >> put_ bh x
  put_ bh (Set s l) = put_ bh False >> put_ bh (nonDetEltsUniqSet s) >> put_ bh l

  get bh = do
    n <- get bh
    if n
      then Dom <$> get bh
      else Set . mkUniqSet <$> get bh <*> get bh

instance Monad m => Refined (K l) m where
  domain (Dom x) = return [x]
  domain _ = return []

  rename x y (Dom x')
    | x == x' = return (Dom y)
  rename _ _ c = return c

-- Is a pair of constructor sets safe?
safe :: K l -> K r -> Bool
safe (Set ks _) (Set ks' _) = uniqSetAll (`elementOfUniqSet` ks') ks
safe (Con k _) (Set ks _) = elementOfUniqSet k ks
safe (Set ks _) (Con k _) = nonDetEltsUniqSet ks == [k]
safe _ _ = True

-- Convert constraint to atomic form
toAtomic :: K l -> K r -> DataType Name -> Maybe [Atomic]
toAtomic (Dom x) (Dom y) d
  | x /= y = Just [Constraint (Dom x) (Dom y) d]
toAtomic (Dom x) (Set k l) d =
  Just [Constraint (Dom x) (Set k l) d]
toAtomic (Set ks l) (Dom x) d =
  Just [Constraint (Con k l) (Dom x) d | k <- nonDetEltsUniqSet ks]
toAtomic (Con k l) (Dom x) d =
  Just [Constraint (Con k l) (Dom x) d]
toAtomic k1 k2 _
  | safe k1 k2 = Just []
  | otherwise = Nothing

constraintLoc :: K l -> Maybe SrcSpan
constraintLoc (Dom _) = Nothing
constraintLoc (Set _ l) = Just l
constraintLoc (Con _ l) = Just l

cons :: K l -> [Name]
cons (Dom _) = []
cons (Con k _) = [k]
cons (Set ks _) = nonDetEltsUniqSet ks

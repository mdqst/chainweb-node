{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language DeriveTraversable #-}
{-# language DerivingStrategies #-}
{-# language InstanceSigs #-}
{-# language LambdaCase #-}
{-# language TupleSections #-}

module Chainweb.Utils.Rule
  ( Rule(..)
  , ruleHead
  , ruleDropWhile
  , ruleTakeWhile
  , ruleValid
  , ruleElems
  , RuleZipper(..)
  , ruleZipZipper
  , unzipRule
  , ruleZipperFind
  , ruleFind

  ) where

import Control.DeepSeq

import Data.Aeson
import Data.Bifunctor
import Data.Hashable
import qualified Data.List.NonEmpty as NE
import Data.Functor.Apply
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import qualified Data.Vector as V

import GHC.Generics

-- | `a` values graded by `h`, starting with the highest `h` value and lowering
-- as you go deeper, bottoming out with no `h` value at all. Used to efficiently
-- represent behaviors that change as the block height increases.
--
-- Is is optimized for lookups of items at the top of stack. On the blockchain
-- we often lookup chain properties (e.g. forks) where we are interested in the
-- latest occurrence.
--
data Rule h a = Above (h, a) (Rule h a) | Bottom a
    deriving stock (Eq, Ord, Show, Foldable, Functor, Generic, Generic1, Traversable)
    deriving anyclass (Hashable, NFData)

instance Bifunctor Rule where
  bimap :: (h -> h') -> (a -> a') -> Rule h a -> Rule h' a'
  bimap fh fa = go
    where
      go = \case
        Above (h, a) r -> Above (fh h, fa a) (go r)
        Bottom a -> Bottom (fa a)

instance Foldable1 (Rule h) where foldMap1 = foldMap1Default
instance Traversable1 (Rule h) where
    traverse1 f (Above (h, a) t) = Above <$> ((h,) <$> f a) <.> traverse1 f t
    traverse1 f (Bottom a) = Bottom <$> f a

instance (ToJSON h, ToJSON a) => ToJSON (Rule h a) where
    toJSON = toJSON . go
      where
        go (Above (h, a) t) = toJSON (toJSON h, toJSON a) : go t
        go (Bottom a) = [toJSON a]

instance (FromJSON h, FromJSON a) => FromJSON (Rule h a) where
    parseJSON = withArray "Rule" $ go . V.toList
      where
        go [] = fail "empty list"
        go [a] = Bottom <$> parseJSON a
        go (x:xs) = Above <$> parseJSON x <*> go xs

ruleHead :: Rule h a -> (Maybe h, a)
ruleHead (Above (h, a) _) = (Just h, a)
ruleHead (Bottom a) = (Nothing, a)

ruleTakeWhile :: (h -> Bool) -> Rule h a -> Rule h a
ruleTakeWhile p (Above (h, a) t)
    | p h = Above (h, a) (ruleTakeWhile p t)
    | otherwise = ruleTakeWhile p t
ruleTakeWhile _ t = t

ruleDropWhile :: (h -> Bool) -> Rule h a -> Rule h a
ruleDropWhile p (Above (h, a) t)
    | p h = ruleDropWhile p t
    | otherwise = Above (h, a) t
ruleDropWhile _ t = t

-- | A zipper on a rule represents a measurement on the rule, either at some
-- point on the rule (including the top) or at the bottom of the rule.
-- Leftmost fields are "below", rightmost fields are "above", relative
-- to the value "here".
data RuleZipper h a
  = BetweenZipper (Rule h a) (h, a) [(h, a)]
  | BottomZipper a [(h, a)]

-- | Construct a zipper at the top of the Rule, O(1).
unzipRule :: Rule h a -> RuleZipper h a
unzipRule (t `Above` tl) = BetweenZipper tl t []
unzipRule (Bottom h) = BottomZipper h []
{-# inline unzipRule #-}

-- | Find the place in the rule zipper that satisfies the condition.
-- Note that if it reaches the bottom, the bottom is returned.
-- O(length(untrue prefix)).
ruleZipperFind :: (h -> a -> Bool) -> RuleZipper h a -> RuleZipper h a
ruleZipperFind p = go
  where
  go pl@(BetweenZipper l (h, a) _)
    | p h a = pl
    | otherwise = go (unzipRule l)
  go pl@(BottomZipper _ _) = pl
{-# inline ruleZipperFind #-}

-- | Find the place in the rule that satisfies the condition, and
-- return it as a zipper.
-- Note that if it reaches the bottom, the bottom is returned.
-- O(length(untrue prefix)).
ruleFind :: (h -> a -> Bool) -> Rule h a -> RuleZipper h a
ruleFind p = ruleZipperFind p . unzipRule
{-# inline ruleFind #-}

-- | Returns the elements of the Rule. O(n) and lazily produces elements.
--
ruleElems :: h -> Rule h a -> NE.NonEmpty (h, a)
ruleElems h (Bottom a) = (h, a) NE.:| []
ruleElems he (Above (h, a) t) = (h, a) `NE.cons` ruleElems he t

-- | Checks that a Rule is decreasing, and thus valid.
-- O(n).
ruleValid :: Ord h => Rule h a -> Bool
ruleValid (Above (h, _) t@(Above (h', _) _)) = h > h' && ruleValid t
ruleValid _ = True

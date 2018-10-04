{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lib where

import Data.Bits
import Data.Biapplicative
import Control.Monad
import Data.Bifunctor
import Data.Set (Set)
import qualified Data.Set as S
import Data.Foldable
import qualified Data.List as L

-- | A conjunction is simply modeled as a list
newtype Conj a = Conj { runConj :: [a] } deriving (Functor, Foldable)

evalConj :: Conj Bool -> Bool
evalConj = and . runConj

-- | Contains @[1..3]@ values
data Upto3 a = Upto1 a | Upto2 a a | Upto3 a a a deriving (Functor)

instance Foldable Upto3 where
  foldr f x  (Upto1 y) = f y x
  foldr f x  (Upto2 y z) = f y (f z x)
  foldr f x ~(Upto3 y z w) = f y (f z (f w x))


-- | Disjunction of up to three values
type Disj3 a = Upto3 a

evalDisj3 :: Disj3 Bool -> Bool
evalDisj3 (Upto1 x) = x
evalDisj3 (Upto2 x y) = x || y
evalDisj3 (Upto3 x y z) = x || y || z

-- | Variables
--
-- @
--  False -> a
--  True -> not a
-- @
--
newtype Var a = Var { runVar :: (Bool, a) }

evalVar :: Var Bool -> Bool
evalVar (Var (b, x)) = b `xor` x

-- | 3-Sat expressions
type Sat3 a = Conj (Disj3 (Var a))

evalSat3 :: Sat3 Bool -> Bool
evalSat3 = evalConj . fmap (evalDisj3 . fmap evalVar)

data Universe a = Universe
  { vars :: Set a
  , completeVars :: Set a
  , expr :: Sat3 a
  , superExprs :: [Sat3 a]
  }

evalUniverse :: Universe Bool -> Bool
evalUniverse = evalSat3 . expr

-- | Pick a var if one exists
-- pickVar :: Universe a -> Maybe (a, Universe a)

-- | Pick a complete var if one exists, removing it from the `Set`
-- of `completeVars`
pickCompleteVar :: Universe a -> Maybe (a, Universe a)
pickCompleteVar u@Universe {..} =
  fmap (\completeVars' -> u {completeVars = completeVars'}) <$>
  S.minView completeVars

-- | Partition into variables adjacent and non-adjacent to the given one
adjacentTo :: Ord a => a -> Sat3 a -> (Set a, Set a)
adjacentTo var = foldr (biliftA2 (<>) (<>)) (mempty, mempty) . fmap (adjacentToDisj3 var . fmap (snd . runVar))

-- | `adjacentTo` for `Disj3`
adjacentToDisj3 :: Ord a => a -> Disj3 a -> (Set a, Set a)
adjacentToDisj3 x = S.partition (== x) . S.fromList . toList

-- | Partition `Sat3` into adjacent and non-adjacent subexpressions
filterAdj :: Ord a => a -> Sat3 a -> (Sat3 a, Sat3 a)
filterAdj var = bimap Conj Conj . L.partition (any ((== var) . snd . runVar) . toList) . runConj

-- | `undefined`
--
-- Choose a variable to split the `Universe` on
filterByVar :: Ord a => a -> Universe a -> Universe a
filterByVar var universe@Universe {..} =
  Universe
    { vars = vars'
    , completeVars = completeVars S.\\ anyNotAdj
    , expr = expr'
    , superExprs = superExpr : superExprs
    }
  where
    ~(vars', anyNotAdj) = adjacentTo var $ (undefined :: Set a -> Sat3 a) vars
    ~(expr', superExpr) = filterAdj var expr

-- | A pass on adjacent variables in a 3-SAT expression:
--
-- @
--  Any vars that are not adjacent to @var@ are removed from @vars@
--
--  If @var@ is adjacent to any @var'@ that has an instance that is not adjacent to any instance of @var@,
--    then @var'@ is removed from @completeVars@
--
--  The new expression has all subexpressions that contain @var@
--
--  The new @superExprs'@ head is all subexpressions that do not contain @var@
-- @
--
adjacentVarsPass :: ()
adjacentVarsPass = ()

-- | `undefined`
--
-- @
--  f universe = case pickCompleteVar universe of
--    Nothing -> case mergeUp universe of
--      Nothing -> universe
--      Just universe' -> f universe'
--    Just (var, universe') -> f (filterByVar var universe')
-- @
--
mergeUp :: Ord a => Universe a -> Maybe (Universe a)
mergeUp = undefined


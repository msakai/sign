{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleInstances, CPP #-}

#if MIN_VERSION_lattices(1,4,0)
import Data.Universe.Class (universe) -- from universe-base package
#else
import Algebra.Enumerable (Enumerable (universe)) -- from lattices package
#endif
import qualified Algebra.Lattice as L -- from lattices package
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Data.Either
import Data.List
import Data.Maybe
import Data.Ratio
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Sign as Sign
import Data.Sign (Sign (..))

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

{--------------------------------------------------------------------
  Sign
--------------------------------------------------------------------}

prop_mult_comm =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
    a `Sign.mult` b == b `Sign.mult` a

prop_mult_assoc =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    a `Sign.mult` (b `Sign.mult` c) == (a `Sign.mult` b) `Sign.mult` c

prop_mult_unitL =
  forAll arbitrary $ \a ->
    Pos `Sign.mult` a == a

prop_mult_unitR =
  forAll arbitrary $ \a ->
    a `Sign.mult` Pos == a

prop_mult_signOf_comm =
  forAll arbitrary $ \(a::Rational) ->
  forAll arbitrary $ \b ->
    Sign.signOf (a * b) == Sign.signOf a `Sign.mult` Sign.signOf b

prop_negate_involution =
  forAll arbitrary $ \a ->
    Sign.negate (Sign.negate a) == a

prop_negate_signOf_comm =
  forAll arbitrary $ \(a::Rational) ->
    Sign.signOf (negate a) == Sign.negate (Sign.signOf a)

prop_abs_non_neg =
  forAll arbitrary $ \a ->
    Sign.abs a /= Neg

prop_abs_mult_orig =
  forAll arbitrary $ \a ->
    Sign.abs a `Sign.mult` a == a

prop_abs_idempotent =
  forAll arbitrary $ \a ->
    Sign.abs (Sign.abs a) == Sign.abs a

prop_abs_signOf_comm =
  forAll arbitrary $ \(a::Rational) ->
    Sign.signOf (abs a) == Sign.abs (Sign.signOf a)

prop_recip_div =
  forAll arbitrary $ \a ->
    a /= Zero ==>
      Sign.recip a == Pos `Sign.div` a

prop_div_inv_mult =
  forAll arbitrary $ \a ->
    forAll arbitrary $ \b ->
      b /= Zero ==>
        a == (a `Sign.div` b) `Sign.mult` b

case_recip_Zero = do
  (ret :: Either SomeException Sign) <- try $ evaluate $ Sign.recip Zero
  assertBool "Sign.recip Zero should be error" (isLeft ret)

prop_div_Zero = QM.monadicIO $ do
  a <- QM.pick arbitrary
  (ret :: Either SomeException Sign) <- QM.run $ try $ evaluate $ a `Sign.div` Zero
  QM.assert $ isLeft ret

prop_pow =
  forAll arbitrary $ \a ->
    forAll (choose (0, 10)) $ \(i::Int) ->
      Sign.pow a i == foldl' Sign.mult Pos (replicate i a)

prop_symbol =
  forAll arbitrary $ \a b ->
    a /= b ==> Sign.symbol a /= Sign.symbol b

prop_Show_Read =
  forAll arbitrary $ \(a :: Sign) ->
    read (show a) == a

prop_rnf =
  forAll arbitrary $ \(a :: Sign) ->
    rnf a == ()

prop_universe =
  Set.fromList universe == Set.fromList [Neg,Zero,Pos]

{--------------------------------------------------------------------
  Sign set
--------------------------------------------------------------------}

prop_SetSign_add_comm =
  forAll arbitrary $ \(a :: Set Sign) ->
  forAll arbitrary $ \b ->
    a + b == b + a

prop_SetSign_add_assoc =
  forAll arbitrary $ \(a :: Set Sign) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    a + (b + c) == (a + b) + c

prop_SetSign_add_unitL =
  forAll arbitrary $ \a ->
    Set.singleton Zero + a == a

prop_SetSign_add_unitR =
  forAll arbitrary $ \a ->
    a + Set.singleton Zero == a

prop_SetSign_add_signOf_comm =
  forAll arbitrary $ \(a::Rational) ->
  forAll arbitrary $ \b ->
    Sign.signOf (a+b) `Set.member` (Set.singleton (Sign.signOf a) + Set.singleton (Sign.signOf b))

prop_SetSign_mult_comm =
  forAll arbitrary $ \(a :: Set Sign) ->
  forAll arbitrary $ \b ->
    a * b == b * a

prop_SetSign_mult_assoc =
  forAll arbitrary $ \(a :: Set Sign) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    a * (b * c) == (a * b) * c

prop_SetSign_mult_unitL =
  forAll arbitrary $ \a ->
    Set.singleton Pos * a == a

prop_SetSign_mult_unitR =
  forAll arbitrary $ \a ->
    a * Set.singleton Pos == a

prop_SetSign_mult_signOf_comm =
  forAll arbitrary $ \(a::Rational) ->
  forAll arbitrary $ \b ->
    Sign.signOf (a*b) `Set.member` (Set.singleton (Sign.signOf a) * Set.singleton (Sign.signOf b))

prop_SetSign_negate_involution =
  forAll arbitrary $ \(a :: Set Sign) ->
    negate (negate a) == a

prop_SetSign_abs_non_neg =
  forAll arbitrary $ \(a :: Set Sign) ->
    Neg `Set.notMember` abs a

prop_SetSign_abs_mult_orig =
  forAll arbitrary $ \(a :: Set Sign) ->
    a `Set.isSubsetOf` (abs a * a)

prop_SetSign_abs_idempotent =
  forAll arbitrary $ \(a :: Set Sign) ->
    abs (abs a) == abs a

prop_SetSign_signum_negate_comm =
  forAll arbitrary $ \(a :: Set Sign) ->
    signum (negate a) == negate (signum a)

prop_SetSign_signum_abs_comm =
  forAll arbitrary $ \(a :: Set Sign) ->
    signum (abs a) == abs (signum a)

prop_SetSign_fromInteger =
  forAll arbitrary $ \a ->
  　case a `compare` 0 of
      EQ -> fromInteger a == Set.singleton Zero
      LT -> fromInteger a == Set.singleton Neg
      GT -> fromInteger a == Set.singleton Pos

prop_SetSign_fromRational =
  forAll arbitrary $ \a ->
  　case a `compare` 0 of
      EQ -> fromRational a == Set.singleton Zero
      LT -> fromRational a == Set.singleton Neg
      GT -> fromRational a == Set.singleton Pos

prop_SetSign_recip_involution =
  forAll g $ \(a :: Set Sign) ->
    Zero `Set.notMember` a ==> recip (recip a) == a
  where
    g = elements $ map Set.unions $
          sequence [[Set.singleton s, Set.empty] | s <- [Neg, Zero, Pos]]

prop_SetSign_Lattice_top =
  forAll arbitrary $ \(a :: Set Sign) ->
    a `Set.isSubsetOf` L.top

prop_SetSign_Lattice_bottom =
  forAll arbitrary $ \(a :: Set Sign) ->
    L.bottom `Set.isSubsetOf` a

prop_SetSign_Lattice_Leq_welldefined =
  forAll arbitrary $ \(a :: Set Sign) b ->
    a `L.meetLeq` b == a `L.joinLeq` b

prop_SetSign_pow =
  forAll arbitrary $ \a ->
    forAll (choose (0, 10)) $ \(i::Int) ->
      Sign.pow a i == foldl' Sign.mult Pos (replicate i a)

{--------------------------------------------------------------------
  Read
--------------------------------------------------------------------}

prop_show_read_invariance =
  forAll arbitrary $ \(a::Sign) -> do
    a == read (show a)

{--------------------------------------------------------------------
  Generators
--------------------------------------------------------------------}

instance Arbitrary Sign where
  arbitrary = arbitraryBoundedEnum
  shrink    = shrinkNothing

instance CoArbitrary Sign where
  coarbitrary = coarbitraryEnum

#if !MIN_VERSION_QuickCheck(2,8,2)

instance Arbitrary (Set Sign) where
  arbitrary = elements $ map Set.unions $
                sequence [[Set.singleton s, Set.empty] | s <- [Neg, Zero, Pos]]
  shrink ss = [Set.delete s ss | s <- Set.toList ss]

instance CoArbitrary (Set Sign) where
  coarbitrary ss g = foldr (\s g -> variant (fromEnum s) g) g (Set.toList ss)

#endif

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)

#if !MIN_VERSION_base(4,7,0)

isLeft :: Either a b -> Bool
isLeft (Left  _) = True
isLeft (Right _) = False

isRight :: Either a b -> Bool
isRight (Left  _) = False
isRight (Right _) = True

#endif

module QuickCheck.Gen.GenN where

open import Haskell.Prelude
open import Haskell.Extra.Refinement
open import Haskell.Prim
open import Haskell.System.Random
open import Haskell.Test.QuickCheck.Random
open import Haskell.Test.QuickCheck.Gen
open import Haskell.Test.QuickCheck.Arbitrary
open import Haskell.Test.QuickCheck.Property

record GenN (a : Type) : Type where 
  no-eta-equality; pattern
  constructor MkGenN
  field 
    unGenN : QCGen → Nat → a

open GenN public

{-# COMPILE AGDA2HS GenN newtype #-}

iDefaultFunctorGenN : DefaultFunctor GenN
iDefaultFunctorGenN .DefaultFunctor.fmap f (MkGenN h) = MkGenN (λ r n → f (h r n))

instance
  iFunctorGenN : Functor GenN
  iFunctorGenN = record { DefaultFunctor iDefaultFunctorGenN }

{-# COMPILE AGDA2HS iFunctorGenN #-}


iDefaultApplicativeGenN : DefaultApplicative GenN
iDefaultApplicativeGenN .DefaultApplicative.pure x = MkGenN (λ _ _ → x)
iDefaultApplicativeGenN .DefaultApplicative._<*>_ (MkGenN gf) (MkGenN ga) = MkGenN (λ r s →
  let (r1 , r2) = splitImpl r
  in gf r1 s (ga r2 s))

instance
  iApplicativeGenN : Applicative GenN
  iApplicativeGenN = record { DefaultApplicative iDefaultApplicativeGenN }

{-# COMPILE AGDA2HS iApplicativeGenN #-}


iDefaultMonadGenN : DefaultMonad GenN
iDefaultMonadGenN .DefaultMonad._>>=_ (MkGenN g) f = MkGenN (λ r s →
  let (r1 , r2) = splitImpl r
  in case f (g r1 s) of λ { (MkGenN m) → m r2 s })

instance
  iMonadGenN : Monad GenN
  iMonadGenN = record { DefaultMonad iDefaultMonadGenN }

{-# COMPILE AGDA2HS iMonadGenN #-}


-- Compiles to the `fromIntegral' function of the Integral type class
fromIntegralIntToNat : ∃ Int IsNonNegativeInt → Nat
fromIntegralIntToNat (n ⟨ p ⟩) = intToNat n ⦃ p ⦄

private
  -- Compiles to the `fromIntegral' function of the Integral type class
  -- Only properly works for Nat's less than 2^63, which is why it is private
  postulate
    fromIntegralNatToInt : Nat → ∃ Int IsNonNegativeInt 
    unsafeIntToNat' : Int → Nat

toGen : GenN a → Gen a
toGen (MkGenN f) = MkGen (λ qcg n → f qcg (fromIntegralIntToNat n))

{-# COMPILE AGDA2HS toGen #-}

-- Only properly works for sizes less than 2^63
toGenN : Gen a → GenN a
toGenN (MkGen f) = MkGenN (λ qcg n → f qcg (fromIntegralNatToInt n))

{-# COMPILE AGDA2HS toGenN #-}


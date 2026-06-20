module Haskell.Test.QuickCheck.Gen where

open import Haskell.Prelude
open import Haskell.Law.Equality
open import Haskell.Extra.Refinement
open import Haskell.Test.QuickCheck.Random
open import Haskell.System.Random

record Gen (a : Type) : Type where 
  no-eta-equality; pattern
  constructor MkGen
  field 
    unGen : QCGen → ∃ Int IsNonNegativeInt → a

open Gen ⦃ ... ⦄ public


iDefaultFunctorGen : DefaultFunctor Gen
iDefaultFunctorGen .DefaultFunctor.fmap f (MkGen h) = MkGen (λ r n → f (h r n))

instance
  iFunctorGen : Functor Gen
  iFunctorGen = record { DefaultFunctor iDefaultFunctorGen }

iDefaultApplicativeGen : DefaultApplicative Gen
iDefaultApplicativeGen .DefaultApplicative.pure x = MkGen (λ _ _ → x)
iDefaultApplicativeGen .DefaultApplicative._<*>_ (MkGen gf) (MkGen ga) = MkGen (λ r s →
  let (r1 , r2) = splitImpl r
  in gf r1 s (ga r2 s))
  
instance
  iApplicativeGen : Applicative Gen
  iApplicativeGen = record { DefaultApplicative iDefaultApplicativeGen }

iDefaultMonadGen : DefaultMonad Gen
iDefaultMonadGen .DefaultMonad._>>=_ (MkGen g) f = MkGen (λ r s →
  let (r1 , r2) = splitImpl r
  in case f (g r1 s) of λ { (MkGen m) → m r2 s })

instance
  iMonadGen : Monad Gen
  iMonadGen = record { DefaultMonad iDefaultMonadGen }


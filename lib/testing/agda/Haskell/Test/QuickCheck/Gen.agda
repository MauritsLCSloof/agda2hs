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

sized : (∃ Int IsNonNegativeInt → Gen a) → Gen a
sized f = MkGen (λ r n → case f n of λ { (MkGen m) → m r n })

getSize : Gen (∃ Int IsNonNegativeInt)
getSize = sized pure

resize : ∃ Int IsNonNegativeInt → Gen a → Gen a
resize n (MkGen g) = MkGen (λ r _ → g r n)

scale : (∃ Int IsNonNegativeInt → ∃ Int IsNonNegativeInt) → Gen a → Gen a
scale f g = sized (λ n → resize (f n) g)

@0 _<=_<=_ : ⦃ Ord a ⦄ → a → a → a → Type
lo <= v <= hi = IsTrue (lo <= v) × IsTrue (v <= hi)

postulate
  choose : ⦃ Random a ⦄ → a × a → Gen a
  chooseAny : ⦃ Random a ⦄ → Gen a
  chooseInt : (range : Int × Int) → Gen Int 
  chooseInt' : (range : Int × Int) → @0 ⦃ IsTrue (fst range <= snd range) ⦄ → Gen (∃ Int (fst range <=_<= snd range))
  chooseEnum : ⦃ Enum a ⦄ → (range : a × a) → Gen a 
  chooseInteger : (range : Integer × Integer) → Gen Integer
  chooseInteger' : (range : Integer × Integer) → @0 ⦃ IsTrue (fst range <= snd range) ⦄ → Gen (∃ Integer (fst range <=_<= snd range))

postulate
  generate : Gen a → IO a
  sample' : Gen a → IO (List a)
  sample : ⦃ Show a ⦄ → Gen a → IO ⊤
  genDouble : Gen (∃ Double (0.0 <=_<= 1.0))
  suchThat : Gen a → (P : a → Bool) → Gen (∃ a (λ x → IsTrue (P x)))
  suchThatMap : Gen a → (a → Maybe b) → Gen b
  suchThatMaybe : Gen a → (P : a → Bool) → Gen (Maybe (∃ a (λ x → IsTrue (P x))))
  oneof : ∃ (List (Gen a)) NonEmpty → Gen a
  frequency :  ∃ (List ((∃ Int IsNonNegativeInt) × Gen a)) NonEmpty → Gen a -- law: probabilities cannot all be zero
  elements : ∃ (List a) NonEmpty → Gen a
  sublistOf : List a → Gen (List a)   -- law: all elements of result are in input, not implemented as it would require Ord
  shuffle : List a → Gen (List a)     -- law: all elements of result are in input and vice versa, not implemented as it would require Ord
  growingElements : ∃ (List a) NonEmpty → Gen a
  listOf : Gen a → Gen (List a)
  listOf1 : Gen a → Gen (List a)
  vectorOf : Int → Gen a → Gen (List a)


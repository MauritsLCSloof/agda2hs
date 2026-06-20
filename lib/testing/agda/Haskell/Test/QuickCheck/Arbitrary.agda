module Haskell.Test.QuickCheck.Arbitrary where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Extra.Refinement

open import Haskell.Test.QuickCheck.Gen
open import Haskell.Test.QuickCheck.Random

record Arbitrary (a : Type) : Type where
  field
    arbitrary : Gen a
    shrink : a → List a

open Arbitrary ⦃ ... ⦄ public


{-# COMPILE AGDA2HS Arbitrary existing-class #-}

instance
  iArbitraryUnit : Arbitrary ⊤
  iArbitraryUnit .arbitrary = return tt
  iArbitraryUnit .shrink _ = []


  iArbitraryBool : Arbitrary Bool
  iArbitraryBool .arbitrary = chooseEnum (False , True)
  iArbitraryBool .shrink True = False ∷ []
  iArbitraryBool .shrink False = []

postulate
  instance
    iArbitraryInteger : Arbitrary Integer
    iArbitraryOrdering : Arbitrary Ordering
    iArbitraryInt : Arbitrary Int
    iArbitraryWord : Arbitrary Word
    iArbitraryDouble : Arbitrary Double
    iArbitraryChar : Arbitrary Char
    iArbitraryQCGen : Arbitrary QCGen
    iArbitraryList : ⦃ Arbitrary a ⦄ → Arbitrary (List a)
    iArbitrary2Tuple : ⦃ Arbitrary a ⦄ → ⦃ Arbitrary b ⦄ → Arbitrary (a × b)
    iArbitrary3Tuple : ⦃ Arbitrary a ⦄ → ⦃ Arbitrary b ⦄ → ⦃ Arbitrary c ⦄ → Arbitrary (a × b × c)
    iArbitrary4Tuple : ⦃ Arbitrary a ⦄ → ⦃ Arbitrary b ⦄ → ⦃ Arbitrary c ⦄ → ⦃ Arbitrary d ⦄ → Arbitrary (a × b × c × d)
    iArbitrary5Tuple : ⦃ Arbitrary a ⦄ → ⦃ Arbitrary b ⦄ → ⦃ Arbitrary c ⦄ → ⦃ Arbitrary d ⦄ → ⦃ Arbitrary e ⦄ → Arbitrary (a × b × c × d × e)
    iArbitrary6Tuple : {f : Type} → ⦃ Arbitrary a ⦄ → ⦃ Arbitrary b ⦄ → ⦃ Arbitrary c ⦄ → ⦃ Arbitrary d ⦄ → ⦃ Arbitrary e ⦄ → ⦃ Arbitrary f ⦄ → Arbitrary (a × b × c × d × e × f)
    iArbitrary7Tuple : {f g : Type} → ⦃ Arbitrary a ⦄ → ⦃ Arbitrary b ⦄ → ⦃ Arbitrary c ⦄ → ⦃ Arbitrary d ⦄ → ⦃ Arbitrary e ⦄ → ⦃ Arbitrary f ⦄ → ⦃ Arbitrary g ⦄ → Arbitrary (a × b × c × d × e × f × g)
    iArbitrary8Tuple : {f g h : Type} → ⦃ Arbitrary a ⦄ → ⦃ Arbitrary b ⦄ → ⦃ Arbitrary c ⦄ → ⦃ Arbitrary d ⦄ → ⦃ Arbitrary e ⦄ → ⦃ Arbitrary f ⦄ → ⦃ Arbitrary g ⦄ → ⦃ Arbitrary h ⦄ → Arbitrary (a × b × c × d × e × f × g × h)
    iArbitrary9Tuple : {f g h i : Type} → ⦃ Arbitrary a ⦄ → ⦃ Arbitrary b ⦄ → ⦃ Arbitrary c ⦄ → ⦃ Arbitrary d ⦄ → ⦃ Arbitrary e ⦄ → ⦃ Arbitrary f ⦄ → ⦃ Arbitrary g ⦄ → ⦃ Arbitrary h ⦄ → ⦃ Arbitrary i ⦄ → Arbitrary (a × b × c × d × e × f × g × h × i)
    iArbitrary10Tuple : {f g h i j : Type} → ⦃ Arbitrary a ⦄ → ⦃ Arbitrary b ⦄ → ⦃ Arbitrary c ⦄ → ⦃ Arbitrary d ⦄ → ⦃ Arbitrary e ⦄ → ⦃ Arbitrary f ⦄ → ⦃ Arbitrary g ⦄ → ⦃ Arbitrary h ⦄ → ⦃ Arbitrary i ⦄ → ⦃ Arbitrary j ⦄ → Arbitrary (a × b × c × d × e × f × g × h × i × j)
    -- QuickCheck does not support tuples bigger than 10

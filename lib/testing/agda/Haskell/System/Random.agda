module Haskell.System.Random where

open import Haskell.Prelude

-- This is not a faithful copy, all functions assume `g' implements RandomGen, 
-- but RandomGen is not ported and thus the precondition is left out
record Random (a : Type) : Type₁ where
  no-eta-equality
  field
    randomR  : { g : Type } → (a × a) → g → (a × g)
    random   : { g : Type } → g → (a × g)
    randomRs : { g : Type } → (a × a) → g → List a
    randoms  : { g : Type } → g → List a

open Random ⦃ ... ⦄ public

postulate
  instance
    iRandomBool    : Random Bool
    iRandomChar    : Random Char
    iRandomDouble  : Random Double
    iRandomInt     : Random Int
    iRandomInteger : Random Integer 
    iRandomWord    : Random Word

{-# COMPILE AGDA2HS Random existing-class #-}


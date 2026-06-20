module Haskell.Test.QuickCheck.Random where

open import Haskell.Prelude

data QCGen : Type where
  MkQCGen : QCGen

postulate   
  splitImpl : QCGen → QCGen × QCGen

module Haskell.Test.QuickCheck.Test where

open import Haskell.Prelude
open import Haskell.Test.QuickCheck.Property

postulate
  quickCheck : ⦃ Testable a ⦄ → a → IO ⊤


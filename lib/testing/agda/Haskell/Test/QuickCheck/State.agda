module Haskell.Test.QuickCheck.State where

open import Haskell.Prelude

record State : Type where
  constructor MkState

record Confidence : Type where
  constructor MkConfidence
  field
    certainty : Integer
    tolerance : Double

postulate instance iConfidenceShow : Show Confidence

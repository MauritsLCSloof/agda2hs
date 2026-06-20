module Haskell.Test.QuickCheck.Property where

open import Haskell.Prelude

open import Haskell.Test.QuickCheck.Gen
open import Haskell.Test.QuickCheck.State
open import Haskell.Test.QuickCheck.Arbitrary


{-# NO_POSITIVITY_CHECK #-}
data Rose (a : Type) : Type where
  MkRose : a → List (Rose a) → Rose a
  IORose : IO (Rose a) → Rose a

data CallbackKind : Type where
  Counterexample : CallbackKind
  NotCounterexample : CallbackKind
  
private mutual 
  {-# NO_POSITIVITY_CHECK #-}
  data Callback : Type where
    PostTest : CallbackKind → (State → Result → IO ⊤) → Callback
    PostFinalFailure : CallbackKind → (State → Result → IO ⊤) → Callback

  {-# NO_POSITIVITY_CHECK #-}
  record Result : Type where
    no-eta-equality
    constructor MkResult
    field
      ok                  : Maybe Bool
      expect              : Bool
      reason              : String
      theException        : Maybe ⊤   -- instead of Maybe AnException
      abort               : Bool
      maybeNumTests       : Maybe Int
      maybeCheckCoverage  : Maybe Confidence
      maybeDiscardedRatio : Maybe Int
      maybeMaxShrinks     : Maybe Int
      maybeMaxTestSize    : Maybe Int
      labels              : List String
      classes             : List (String × Bool)
      tables              : List (String × String)
      requiredCoverage    : List (Maybe String × String × Double)
      callbacks           : List Callback
      testCase            : List String

open Result public

data Prop : Type where 
  MkProp : Rose Result → Prop

record Property : Type where 
  constructor MkProperty
  field
    unProperty : Gen Prop


record Testable (prop : Type) : Type₁ where
  field
    property : prop → Property
    propertyForAllShrinkShow : Gen a → (a → (List a)) → (a → (List String)) → (a → prop) → Property


{-# COMPILE AGDA2HS Testable existing-class #-}

private postulate
  propertyForAllShrinkShowImpl : {prop : Type} → Gen a → (a → (List a)) → (a → (List String)) → (a → prop) → Property

record DefaultTestable (prop : Type) : Type₁ where
  field 
    property : prop → Property

  propertyForAllShrinkShow : Gen a → (a → (List a)) → (a → (List String)) → (a → prop) → Property
  propertyForAllShrinkShow g s sh ap = propertyForAllShrinkShowImpl g s sh ap

open Testable ⦃ ... ⦄  public


data Discard : Type where
  MkDiscard : Discard    -- constructor has the same name as type in QuickCheck

postulate
  instance
    iTestableDiscard  : Testable Discard
    iTestable⊤        : Testable ⊤
    iTestableBool     : Testable Bool
    iTestableResult   : Testable Result
    iTestableProp     : Testable Prop
    iTestableProperty : Testable Property
    iTestableGen      : ⦃ Testable a ⦄ → Testable (Gen a)
    iTestableMaybe    : ⦃ Testable a ⦄ → Testable (Maybe a)
    iTestableFun      : {prop : Type} → ⦃ Arbitrary a ⦄ → ⦃ Show a ⦄ → ⦃ Testable prop ⦄ → Testable (a → prop)


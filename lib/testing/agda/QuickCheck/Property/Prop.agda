module QuickCheck.Property.Prop where

open import Haskell.Prelude
open import Haskell.Extra.Refinement
open import Haskell.Test.QuickCheck.Property
open import Haskell.Test.QuickCheck.Gen
open import QuickCheck.Gen.GenN
open import QuickCheck.Random.Prop
open import Haskell.Test.QuickCheck.Random
open import Haskell.Extra.Dec
open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality
open import Haskell.Prim

@0 _corresponds-to_ : (a → Type) → (a → Bool) → Type
_corresponds-to_ P pred = ∀ x → Reflects (P x) (pred x)

@0 _corresponds-to-2_ : (a → b → Type) → (a → b → Bool) → Type
_corresponds-to-2_ P pred = ∀ x y → Reflects (P x y) (pred x y)

@0 _corresponds-to-3_ : (a → b → c → Type) → (a → b → c → Bool) → Type
_corresponds-to-3_ P pred = ∀ x y z → Reflects (P x y z) (pred x y z)

@0 _corresponds-to-4_ : (a → b → c → d → Type) → (a → b → c → d → Bool) → Type
_corresponds-to-4_ P pred = ∀ x y z w → Reflects (P x y z w) (pred x y z w)

@0 _corresponds-to-5_ : (a → b → c → d → e → Type) → (a → b → c → d → e → Bool) → Type
_corresponds-to-5_ P pred = ∀ x y z w v → Reflects (P x y z w v) (pred x y z w v)
  
reflectsIsTrue : (b : Bool) → Reflects (IsTrue b) b
reflectsIsTrue True  = IsTrue.itsTrue
reflectsIsTrue False = λ ()

useEq : {x y : Bool} → x ≡ y → IsTrue x → IsTrue y
useEq {True} {True} eq is = IsTrue.itsTrue

reverseEq : { x : Bool } → (IsTrue x) → x ≡ True
reverseEq {False} ()
reverseEq {True} input = refl


not-to-→⊥ : ∀ {x : Bool} → IsTrue (not x) → (IsTrue x → ⊥)
not-to-→⊥ {False} p = λ ()
not-to-→⊥ {True} ()

→⊥-to-not : ∀ {x : Bool} → (IsTrue x → ⊥) → IsTrue (not x) 
→⊥-to-not {False} f = IsTrue.itsTrue
→⊥-to-not {True} f = magic (f IsTrue.itsTrue)

&&-to-× : ∀ {x y : Bool} → IsTrue (x && y) → IsTrue x × IsTrue y
&&-to-× {False} ()
&&-to-× {True} p = IsTrue.itsTrue , p

×-to-&& : ∀ {x y : Bool} → IsTrue x × IsTrue y → IsTrue (x && y)
×-to-&& {False} (() , _)
×-to-&& {True} (_ , p) = p

||-to-Either : ∀ {x y : Bool} → IsTrue (x || y) → Either (IsTrue x) (IsTrue y)
||-to-Either {True} p = Left IsTrue.itsTrue
||-to-Either {False} p = Right p

Either-to-|| : ∀ {x y : Bool} → Either (IsTrue x) (IsTrue y) → IsTrue (x || y) 
Either-to-|| {True} _ = IsTrue.itsTrue
Either-to-|| {False} (Left ())
Either-to-|| {False} (Right p) = p


module _ {ty : Type} ⦃ _ : Eq ty ⦄ ⦃ _ : IsLawfulEq ty ⦄ where
  ==-to-≡ : ∀ {x y : ty} → IsTrue (x == y) → x ≡ y
  ==-to-≡ {x} {y} p = equality x y (reverseEq p)

  ≡-to-== : ∀ {x y : ty} → x ≡ y → IsTrue (x == y)
  ≡-to-== {x} {y} h = useEq (sym (equality' x y h)) IsTrue.itsTrue

  /=-to-≡→⊥ : ∀ {x y : ty} → IsTrue (x /= y) → ((x ≡ y) → ⊥)
  /=-to-≡→⊥ {x} {y} p h = not-to-→⊥ {x == y} p (≡-to-== h)
    
  ≡→⊥-to-/= : ∀ {x y : ty} → ((x ≡ y) → ⊥) → IsTrue (x /= y)
  ≡→⊥-to-/= {x} {y} h = →⊥-to-not {x == y} (λ q → h (==-to-≡ q))


-- Based on Data.Either.Combinators, rebase Rebase.Prelude
mapBoth : (a → c) → (b → d) → Either a b → Either c d
mapBoth f _ (Left v) = Left (f v)
mapBoth _ f (Right v) = Right (f v)


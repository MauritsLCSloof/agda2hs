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


sizedN : (Nat → GenN a) → GenN a
sizedN f = MkGenN (λ r n → case f n of λ { (MkGenN m) → m r n })

{-# COMPILE AGDA2HS sizedN #-}


getSizeN : GenN Nat
getSizeN = sizedN pure

{-# COMPILE AGDA2HS getSizeN #-}


resizeN : Nat → GenN a → GenN a
resizeN n (MkGenN g) = MkGenN (λ r _ → g r n)

{-# COMPILE AGDA2HS resizeN #-}


scaleN : (Nat → Nat) → GenN a → GenN a
scaleN f g = sizedN (λ n → resizeN (f n) g)

{-# COMPILE AGDA2HS scaleN #-}


chooseN : ⦃ Random a ⦄ → a × a → GenN a
chooseN = toGenN ∘ choose

{-# COMPILE AGDA2HS chooseN #-}


chooseAnyN : ⦃ Random a ⦄ → GenN a
chooseAnyN = toGenN chooseAny

{-# COMPILE AGDA2HS chooseAnyN #-}


chooseIntN : (range : Int × Int) → GenN Int
chooseIntN r = toGenN (chooseInt r)

{-# COMPILE AGDA2HS chooseIntN #-}


chooseIntN' : (range : Int × Int) → @0 ⦃ IsTrue (fst range <= snd range) ⦄ → GenN (∃ Int (fst range <=_<= snd range))
chooseIntN' r = toGenN (chooseInt' r)

{-# COMPILE AGDA2HS chooseIntN' #-}


chooseNat : (range : Nat × Nat) → Gen Nat
chooseNat (lo , hi) = unsafeIntToNat' <$> (chooseInt (value (fromIntegralNatToInt lo) , value (fromIntegralNatToInt hi)))

{-# COMPILE AGDA2HS chooseNat #-}


chooseNatN : (range : Nat × Nat) → GenN Nat
chooseNatN (lo , hi) = unsafeIntToNat' <$> chooseIntN (value $ fromIntegralNatToInt lo , value $ fromIntegralNatToInt hi)

{-# COMPILE AGDA2HS chooseNatN #-}

instance
  iArbitraryNat : Arbitrary Nat
  iArbitraryNat .arbitrary = toGen (sizedN $ λ n → chooseNatN (0 , n))
  iArbitraryNat .shrink n = map (unsafeIntToNat') (shrink (value $ fromIntegralNatToInt n))

{-# COMPILE AGDA2HS iArbitraryNat #-}

chooseEnumN : ⦃ Enum a ⦄ → (range : a × a) → GenN a
chooseEnumN r = toGenN (chooseEnum r)

{-# COMPILE AGDA2HS chooseEnumN #-}


chooseIntegerN : (range : Integer × Integer) → GenN Integer
chooseIntegerN r = toGenN (chooseInteger r)

{-# COMPILE AGDA2HS chooseIntegerN #-}


chooseIntegerN' : (range : Integer × Integer) → @0 ⦃ IsTrue (fst range <= snd range) ⦄ → GenN (∃ Integer (fst range <=_<= snd range))
chooseIntegerN' r = toGenN (chooseInteger' r)

{-# COMPILE AGDA2HS chooseIntegerN' #-}


generateN : GenN a → IO a
generateN g = generate (toGen g)

{-# COMPILE AGDA2HS generateN #-}


sampleN' : GenN a → IO (List a)
sampleN' g = sample' (toGen g)

{-# COMPILE AGDA2HS sampleN' #-}


sampleN : ⦃ Show a ⦄ → GenN a → IO ⊤
sampleN g = sample (toGen g)

{-# COMPILE AGDA2HS sampleN #-}


genDoubleN : GenN (∃ Double (0.0 <=_<= 1.0))
genDoubleN = toGenN genDouble

{-# COMPILE AGDA2HS genDoubleN #-}


suchThatN : GenN a → (P : a → Bool) → GenN (∃ a (λ x → IsTrue (P x)))
suchThatN g p = toGenN $ suchThat (toGen g) p  

{-# COMPILE AGDA2HS suchThatN #-}


suchThatMapN : GenN a → (a → Maybe b) → GenN b
suchThatMapN g f = toGenN $ suchThatMap (toGen g) f  

{-# COMPILE AGDA2HS suchThatMapN #-}


suchThatMaybeN : GenN a → (P : a → Bool) → GenN (Maybe (∃ a (λ x → IsTrue (P x))))
suchThatMaybeN g p = toGenN $ suchThatMaybe (toGen g) p

{-# COMPILE AGDA2HS suchThatMaybeN #-}


private
  @0 nonEmptyMap : ∀ (f : a → b) {xs : List a} → NonEmpty xs → NonEmpty (map f xs)
  nonEmptyMap _ itsNonEmpty = itsNonEmpty


oneofN : ∃ (List (GenN a)) NonEmpty → GenN a
oneofN (l ⟨ p ⟩) = toGenN $ oneof (map toGen l ⟨ nonEmptyMap toGen p ⟩)

{-# COMPILE AGDA2HS oneofN #-}


-- law: probabilities cannot all be zero
frequencyN : ∃ (List (Nat × GenN a)) NonEmpty → GenN a
frequencyN (gs ⟨ p ⟩) = toGenN $ frequency ((map genNPair2GenPair gs) ⟨ nonEmptyMap genNPair2GenPair p ⟩)
  where
    genNPair2GenPair : (Nat × GenN a) → ((∃ Int IsNonNegativeInt) × Gen a)
    genNPair2GenPair (n , gn) = fromIntegralNatToInt n , toGen gn

{-# COMPILE AGDA2HS frequencyN #-}


elementsN : ∃ (List a) NonEmpty → GenN a
elementsN = toGenN ∘ elements

{-# COMPILE AGDA2HS elementsN #-}


sublistOfN : List a → GenN (List a)
sublistOfN = toGenN ∘ sublistOf

{-# COMPILE AGDA2HS sublistOfN #-}


shuffleN : List a → GenN (List a)
shuffleN = toGenN ∘ shuffle

{-# COMPILE AGDA2HS shuffleN #-}


growingElementsN : ∃ (List a) NonEmpty → GenN a
growingElementsN = toGenN ∘ growingElements

{-# COMPILE AGDA2HS growingElementsN #-}


listOfN : GenN a → GenN (List a)
listOfN = toGenN ∘ listOf ∘ toGen

{-# COMPILE AGDA2HS listOfN #-}


listOf1N : GenN a → GenN (List a)
listOf1N = toGenN ∘ listOf1 ∘ toGen

{-# COMPILE AGDA2HS listOf1N #-}


vectorOfN : Int → GenN a → GenN (List a)
vectorOfN s g = toGenN $ vectorOf s (toGen g)

{-# COMPILE AGDA2HS vectorOfN #-}


module _ {prop : Type} ⦃ _ : Testable prop ⦄ where
  forAllN : ⦃ Show a ⦄ → GenN a → (a → prop) → Property
  forAllN g = forAll (toGen g)

  {-# COMPILE AGDA2HS forAllN #-}

  forAllShowN : GenN a → (a → String) → (a → prop) → Property
  forAllShowN g = forAllShow (toGen g)

  {-# COMPILE AGDA2HS forAllShowN #-}

  forAllBlindN : GenN a → (a → prop) → Property
  forAllBlindN g = forAllBlind (toGen g)

  {-# COMPILE AGDA2HS forAllBlindN #-}

  forAllShrinkN : ⦃ Show a ⦄ → GenN a → (a → List a) → (a → prop) → Property
  forAllShrinkN g = forAllShrink (toGen g)

  {-# COMPILE AGDA2HS forAllShrinkN #-}

  forAllShrinkShowN : ⦃ Show a ⦄ → GenN a → (a → List a) → (a → String) → (a → prop) → Property
  forAllShrinkShowN g = forAllShrinkShow (toGen g)

  {-# COMPILE AGDA2HS forAllShrinkShowN #-}

  forAllShrinkBlindN : ⦃ Show a ⦄ → GenN a → (a → List a) → (a → prop) → Property
  forAllShrinkBlindN g = forAllShrinkBlind (toGen g)

  {-# COMPILE AGDA2HS forAllShrinkBlindN #-}


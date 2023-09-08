------------------------------------------------------------------------
-- A modality for affine types.
------------------------------------------------------------------------

open import Tools.Bool
open import Tools.Level

open import Graded.Modality.Instances.Zero-one-many true as 𝟘𝟙ω
open import Graded.Modality.Variant lzero

module Graded.Modality.Instances.Affine
  -- The modality variant.
  (variant : Modality-variant)
  where

open Modality-variant variant

open 𝟘𝟙ω renaming (Zero-one-many to Affine) public

open import Graded.Modality Affine
open import Graded.FullReduction.Assumptions

open import Definition.Typed.Restrictions Affine

open import Tools.Empty
open import Tools.Function
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum
open import Tools.Unit

private variable
  p  : Affine
  rs : Type-restrictions

-- An "affine types" modality.

affineModality : Modality
affineModality = zero-one-many-modality variant

-- An alternative (not very good) "affine types" modality.
--
-- See Graded.Modality.Instances.Affine.Bad for an example that
-- illustrates in what sense this modality is not very good. The
-- modality affineModality does not suffer from this problem (see
-- Graded.Modality.Instances.Affine.Good), but note that, at the time
-- of writing, this formalisation does not contain any solid evidence
-- showing that affineModality captures a good notion of "affine
-- type".

bad-affine-modality : Modality
bad-affine-modality = zero-one-many-greatest variant

-- The nr function obtained from bad-affine-modality (if any) is
-- strictly greater than the one obtained from affineModality.

alternative-greater :
  (nr-available : Nr-available) →
  let nr₁ = affineModality
              .Modality.has-nr nr-available .Has-nr.nr
      nr₂ = bad-affine-modality
              .Modality.has-nr nr-available .Has-nr.nr
  in
  (∃₂ λ p r → ∃₃ λ z s n → ¬ nr₁ p r z s n ≡ nr₂ p r z s n) ×
  (∀ p r z s n → nr₁ p r z s n ≤ nr₂ p r z s n)
alternative-greater _ =
    (𝟘 , 𝟙 , 𝟙 , 𝟘 , 𝟙 , (λ ()))
  , λ where
      𝟘 𝟘 𝟘 𝟘 𝟘 → refl
      𝟘 𝟘 𝟘 𝟘 𝟙 → refl
      𝟘 𝟘 𝟘 𝟘 ω → refl
      𝟘 𝟘 𝟘 𝟙 𝟘 → refl
      𝟘 𝟘 𝟘 𝟙 𝟙 → refl
      𝟘 𝟘 𝟘 𝟙 ω → refl
      𝟘 𝟘 𝟘 ω 𝟘 → refl
      𝟘 𝟘 𝟘 ω 𝟙 → refl
      𝟘 𝟘 𝟘 ω ω → refl
      𝟘 𝟘 𝟙 𝟘 𝟘 → refl
      𝟘 𝟘 𝟙 𝟘 𝟙 → refl
      𝟘 𝟘 𝟙 𝟘 ω → refl
      𝟘 𝟘 𝟙 𝟙 𝟘 → refl
      𝟘 𝟘 𝟙 𝟙 𝟙 → refl
      𝟘 𝟘 𝟙 𝟙 ω → refl
      𝟘 𝟘 𝟙 ω 𝟘 → refl
      𝟘 𝟘 𝟙 ω 𝟙 → refl
      𝟘 𝟘 𝟙 ω ω → refl
      𝟘 𝟘 ω 𝟘 𝟘 → refl
      𝟘 𝟘 ω 𝟘 𝟙 → refl
      𝟘 𝟘 ω 𝟘 ω → refl
      𝟘 𝟘 ω 𝟙 𝟘 → refl
      𝟘 𝟘 ω 𝟙 𝟙 → refl
      𝟘 𝟘 ω 𝟙 ω → refl
      𝟘 𝟘 ω ω 𝟘 → refl
      𝟘 𝟘 ω ω 𝟙 → refl
      𝟘 𝟘 ω ω ω → refl
      𝟘 𝟙 𝟘 𝟘 𝟘 → refl
      𝟘 𝟙 𝟘 𝟘 𝟙 → refl
      𝟘 𝟙 𝟘 𝟘 ω → refl
      𝟘 𝟙 𝟘 𝟙 𝟘 → refl
      𝟘 𝟙 𝟘 𝟙 𝟙 → refl
      𝟘 𝟙 𝟘 𝟙 ω → refl
      𝟘 𝟙 𝟘 ω 𝟘 → refl
      𝟘 𝟙 𝟘 ω 𝟙 → refl
      𝟘 𝟙 𝟘 ω ω → refl
      𝟘 𝟙 𝟙 𝟘 𝟘 → refl
      𝟘 𝟙 𝟙 𝟘 𝟙 → refl
      𝟘 𝟙 𝟙 𝟘 ω → refl
      𝟘 𝟙 𝟙 𝟙 𝟘 → refl
      𝟘 𝟙 𝟙 𝟙 𝟙 → refl
      𝟘 𝟙 𝟙 𝟙 ω → refl
      𝟘 𝟙 𝟙 ω 𝟘 → refl
      𝟘 𝟙 𝟙 ω 𝟙 → refl
      𝟘 𝟙 𝟙 ω ω → refl
      𝟘 𝟙 ω 𝟘 𝟘 → refl
      𝟘 𝟙 ω 𝟘 𝟙 → refl
      𝟘 𝟙 ω 𝟘 ω → refl
      𝟘 𝟙 ω 𝟙 𝟘 → refl
      𝟘 𝟙 ω 𝟙 𝟙 → refl
      𝟘 𝟙 ω 𝟙 ω → refl
      𝟘 𝟙 ω ω 𝟘 → refl
      𝟘 𝟙 ω ω 𝟙 → refl
      𝟘 𝟙 ω ω ω → refl
      𝟘 ω 𝟘 𝟘 𝟘 → refl
      𝟘 ω 𝟘 𝟘 𝟙 → refl
      𝟘 ω 𝟘 𝟘 ω → refl
      𝟘 ω 𝟘 𝟙 𝟘 → refl
      𝟘 ω 𝟘 𝟙 𝟙 → refl
      𝟘 ω 𝟘 𝟙 ω → refl
      𝟘 ω 𝟘 ω 𝟘 → refl
      𝟘 ω 𝟘 ω 𝟙 → refl
      𝟘 ω 𝟘 ω ω → refl
      𝟘 ω 𝟙 𝟘 𝟘 → refl
      𝟘 ω 𝟙 𝟘 𝟙 → refl
      𝟘 ω 𝟙 𝟘 ω → refl
      𝟘 ω 𝟙 𝟙 𝟘 → refl
      𝟘 ω 𝟙 𝟙 𝟙 → refl
      𝟘 ω 𝟙 𝟙 ω → refl
      𝟘 ω 𝟙 ω 𝟘 → refl
      𝟘 ω 𝟙 ω 𝟙 → refl
      𝟘 ω 𝟙 ω ω → refl
      𝟘 ω ω 𝟘 𝟘 → refl
      𝟘 ω ω 𝟘 𝟙 → refl
      𝟘 ω ω 𝟘 ω → refl
      𝟘 ω ω 𝟙 𝟘 → refl
      𝟘 ω ω 𝟙 𝟙 → refl
      𝟘 ω ω 𝟙 ω → refl
      𝟘 ω ω ω 𝟘 → refl
      𝟘 ω ω ω 𝟙 → refl
      𝟘 ω ω ω ω → refl
      𝟙 𝟘 𝟘 𝟘 𝟘 → refl
      𝟙 𝟘 𝟘 𝟘 𝟙 → refl
      𝟙 𝟘 𝟘 𝟘 ω → refl
      𝟙 𝟘 𝟘 𝟙 𝟘 → refl
      𝟙 𝟘 𝟘 𝟙 𝟙 → refl
      𝟙 𝟘 𝟘 𝟙 ω → refl
      𝟙 𝟘 𝟘 ω 𝟘 → refl
      𝟙 𝟘 𝟘 ω 𝟙 → refl
      𝟙 𝟘 𝟘 ω ω → refl
      𝟙 𝟘 𝟙 𝟘 𝟘 → refl
      𝟙 𝟘 𝟙 𝟘 𝟙 → refl
      𝟙 𝟘 𝟙 𝟘 ω → refl
      𝟙 𝟘 𝟙 𝟙 𝟘 → refl
      𝟙 𝟘 𝟙 𝟙 𝟙 → refl
      𝟙 𝟘 𝟙 𝟙 ω → refl
      𝟙 𝟘 𝟙 ω 𝟘 → refl
      𝟙 𝟘 𝟙 ω 𝟙 → refl
      𝟙 𝟘 𝟙 ω ω → refl
      𝟙 𝟘 ω 𝟘 𝟘 → refl
      𝟙 𝟘 ω 𝟘 𝟙 → refl
      𝟙 𝟘 ω 𝟘 ω → refl
      𝟙 𝟘 ω 𝟙 𝟘 → refl
      𝟙 𝟘 ω 𝟙 𝟙 → refl
      𝟙 𝟘 ω 𝟙 ω → refl
      𝟙 𝟘 ω ω 𝟘 → refl
      𝟙 𝟘 ω ω 𝟙 → refl
      𝟙 𝟘 ω ω ω → refl
      𝟙 𝟙 𝟘 𝟘 𝟘 → refl
      𝟙 𝟙 𝟘 𝟘 𝟙 → refl
      𝟙 𝟙 𝟘 𝟘 ω → refl
      𝟙 𝟙 𝟘 𝟙 𝟘 → refl
      𝟙 𝟙 𝟘 𝟙 𝟙 → refl
      𝟙 𝟙 𝟘 𝟙 ω → refl
      𝟙 𝟙 𝟘 ω 𝟘 → refl
      𝟙 𝟙 𝟘 ω 𝟙 → refl
      𝟙 𝟙 𝟘 ω ω → refl
      𝟙 𝟙 𝟙 𝟘 𝟘 → refl
      𝟙 𝟙 𝟙 𝟘 𝟙 → refl
      𝟙 𝟙 𝟙 𝟘 ω → refl
      𝟙 𝟙 𝟙 𝟙 𝟘 → refl
      𝟙 𝟙 𝟙 𝟙 𝟙 → refl
      𝟙 𝟙 𝟙 𝟙 ω → refl
      𝟙 𝟙 𝟙 ω 𝟘 → refl
      𝟙 𝟙 𝟙 ω 𝟙 → refl
      𝟙 𝟙 𝟙 ω ω → refl
      𝟙 𝟙 ω 𝟘 𝟘 → refl
      𝟙 𝟙 ω 𝟘 𝟙 → refl
      𝟙 𝟙 ω 𝟘 ω → refl
      𝟙 𝟙 ω 𝟙 𝟘 → refl
      𝟙 𝟙 ω 𝟙 𝟙 → refl
      𝟙 𝟙 ω 𝟙 ω → refl
      𝟙 𝟙 ω ω 𝟘 → refl
      𝟙 𝟙 ω ω 𝟙 → refl
      𝟙 𝟙 ω ω ω → refl
      𝟙 ω 𝟘 𝟘 𝟘 → refl
      𝟙 ω 𝟘 𝟘 𝟙 → refl
      𝟙 ω 𝟘 𝟘 ω → refl
      𝟙 ω 𝟘 𝟙 𝟘 → refl
      𝟙 ω 𝟘 𝟙 𝟙 → refl
      𝟙 ω 𝟘 𝟙 ω → refl
      𝟙 ω 𝟘 ω 𝟘 → refl
      𝟙 ω 𝟘 ω 𝟙 → refl
      𝟙 ω 𝟘 ω ω → refl
      𝟙 ω 𝟙 𝟘 𝟘 → refl
      𝟙 ω 𝟙 𝟘 𝟙 → refl
      𝟙 ω 𝟙 𝟘 ω → refl
      𝟙 ω 𝟙 𝟙 𝟘 → refl
      𝟙 ω 𝟙 𝟙 𝟙 → refl
      𝟙 ω 𝟙 𝟙 ω → refl
      𝟙 ω 𝟙 ω 𝟘 → refl
      𝟙 ω 𝟙 ω 𝟙 → refl
      𝟙 ω 𝟙 ω ω → refl
      𝟙 ω ω 𝟘 𝟘 → refl
      𝟙 ω ω 𝟘 𝟙 → refl
      𝟙 ω ω 𝟘 ω → refl
      𝟙 ω ω 𝟙 𝟘 → refl
      𝟙 ω ω 𝟙 𝟙 → refl
      𝟙 ω ω 𝟙 ω → refl
      𝟙 ω ω ω 𝟘 → refl
      𝟙 ω ω ω 𝟙 → refl
      𝟙 ω ω ω ω → refl
      ω 𝟘 𝟘 𝟘 𝟘 → refl
      ω 𝟘 𝟘 𝟘 𝟙 → refl
      ω 𝟘 𝟘 𝟘 ω → refl
      ω 𝟘 𝟘 𝟙 𝟘 → refl
      ω 𝟘 𝟘 𝟙 𝟙 → refl
      ω 𝟘 𝟘 𝟙 ω → refl
      ω 𝟘 𝟘 ω 𝟘 → refl
      ω 𝟘 𝟘 ω 𝟙 → refl
      ω 𝟘 𝟘 ω ω → refl
      ω 𝟘 𝟙 𝟘 𝟘 → refl
      ω 𝟘 𝟙 𝟘 𝟙 → refl
      ω 𝟘 𝟙 𝟘 ω → refl
      ω 𝟘 𝟙 𝟙 𝟘 → refl
      ω 𝟘 𝟙 𝟙 𝟙 → refl
      ω 𝟘 𝟙 𝟙 ω → refl
      ω 𝟘 𝟙 ω 𝟘 → refl
      ω 𝟘 𝟙 ω 𝟙 → refl
      ω 𝟘 𝟙 ω ω → refl
      ω 𝟘 ω 𝟘 𝟘 → refl
      ω 𝟘 ω 𝟘 𝟙 → refl
      ω 𝟘 ω 𝟘 ω → refl
      ω 𝟘 ω 𝟙 𝟘 → refl
      ω 𝟘 ω 𝟙 𝟙 → refl
      ω 𝟘 ω 𝟙 ω → refl
      ω 𝟘 ω ω 𝟘 → refl
      ω 𝟘 ω ω 𝟙 → refl
      ω 𝟘 ω ω ω → refl
      ω 𝟙 𝟘 𝟘 𝟘 → refl
      ω 𝟙 𝟘 𝟘 𝟙 → refl
      ω 𝟙 𝟘 𝟘 ω → refl
      ω 𝟙 𝟘 𝟙 𝟘 → refl
      ω 𝟙 𝟘 𝟙 𝟙 → refl
      ω 𝟙 𝟘 𝟙 ω → refl
      ω 𝟙 𝟘 ω 𝟘 → refl
      ω 𝟙 𝟘 ω 𝟙 → refl
      ω 𝟙 𝟘 ω ω → refl
      ω 𝟙 𝟙 𝟘 𝟘 → refl
      ω 𝟙 𝟙 𝟘 𝟙 → refl
      ω 𝟙 𝟙 𝟘 ω → refl
      ω 𝟙 𝟙 𝟙 𝟘 → refl
      ω 𝟙 𝟙 𝟙 𝟙 → refl
      ω 𝟙 𝟙 𝟙 ω → refl
      ω 𝟙 𝟙 ω 𝟘 → refl
      ω 𝟙 𝟙 ω 𝟙 → refl
      ω 𝟙 𝟙 ω ω → refl
      ω 𝟙 ω 𝟘 𝟘 → refl
      ω 𝟙 ω 𝟘 𝟙 → refl
      ω 𝟙 ω 𝟘 ω → refl
      ω 𝟙 ω 𝟙 𝟘 → refl
      ω 𝟙 ω 𝟙 𝟙 → refl
      ω 𝟙 ω 𝟙 ω → refl
      ω 𝟙 ω ω 𝟘 → refl
      ω 𝟙 ω ω 𝟙 → refl
      ω 𝟙 ω ω ω → refl
      ω ω 𝟘 𝟘 𝟘 → refl
      ω ω 𝟘 𝟘 𝟙 → refl
      ω ω 𝟘 𝟘 ω → refl
      ω ω 𝟘 𝟙 𝟘 → refl
      ω ω 𝟘 𝟙 𝟙 → refl
      ω ω 𝟘 𝟙 ω → refl
      ω ω 𝟘 ω 𝟘 → refl
      ω ω 𝟘 ω 𝟙 → refl
      ω ω 𝟘 ω ω → refl
      ω ω 𝟙 𝟘 𝟘 → refl
      ω ω 𝟙 𝟘 𝟙 → refl
      ω ω 𝟙 𝟘 ω → refl
      ω ω 𝟙 𝟙 𝟘 → refl
      ω ω 𝟙 𝟙 𝟙 → refl
      ω ω 𝟙 𝟙 ω → refl
      ω ω 𝟙 ω 𝟘 → refl
      ω ω 𝟙 ω 𝟙 → refl
      ω ω 𝟙 ω ω → refl
      ω ω ω 𝟘 𝟘 → refl
      ω ω ω 𝟘 𝟙 → refl
      ω ω ω 𝟘 ω → refl
      ω ω ω 𝟙 𝟘 → refl
      ω ω ω 𝟙 𝟙 → refl
      ω ω ω 𝟙 ω → refl
      ω ω ω ω 𝟘 → refl
      ω ω ω ω 𝟙 → refl
      ω ω ω ω ω → refl

-- The affine types" modality has a well-behaved zero.

affine-has-well-behaved-zero : Has-well-behaved-zero (Modality.semiring-with-meet affineModality)
affine-has-well-behaved-zero = zero-one-many-has-well-behaved-zero

-- 𝟘 is the largest element.

≤𝟘 : p ≤ 𝟘
≤𝟘 {p = 𝟘} = refl
≤𝟘 {p = 𝟙} = refl
≤𝟘 {p = ω} = refl

-- An instance of Type-restrictions is suitable for the full reduction
-- theorem if
-- * Σₚ-allowed 𝟘 p implies that 𝟘ᵐ is allowed, and
-- * Σₚ-allowed ω p does not hold.

Suitable-for-full-reduction :
  Type-restrictions → Set
Suitable-for-full-reduction rs =
  (∀ p → Σₚ-allowed 𝟘 p → T 𝟘ᵐ-allowed) ×
  (∀ p → ¬ Σₚ-allowed ω p)
  where
  open Type-restrictions rs

-- Given an instance of Type-restrictions one can create a "suitable"
-- instance.

suitable-for-full-reduction :
  Type-restrictions → ∃ Suitable-for-full-reduction
suitable-for-full-reduction rs =
    record rs
      { ΠΣ-allowed = λ b p q →
          ΠΣ-allowed b p q × T 𝟘ᵐ-allowed × p ≢ ω
      }
  , (λ _ → proj₁ ∘→ proj₂)
  , (λ _ → (_$ refl) ∘→ proj₂ ∘→ proj₂)
  where
  open Type-restrictions rs

-- The full reduction assumptions hold for affineModality and any
-- "suitable" Type-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction rs →
  Full-reduction-assumptions affineModality rs
full-reduction-assumptions (𝟘→𝟘ᵐ , ¬ω) = record
  { 𝟙≤𝟘    = λ _ → refl
  ; ≡𝟙⊎𝟙≤𝟘 = λ where
      {p = ω} ok → ⊥-elim (¬ω _ ok)
      {p = 𝟙} _  → inj₁ refl
      {p = 𝟘} ok → inj₂ (refl , 𝟘→𝟘ᵐ _ ok , refl)
  }

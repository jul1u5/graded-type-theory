------------------------------------------------------------------------
-- Lemmas related to
-- Are-preserving-type-restrictions/Are-reflecting-type-restrictions
-- and specific type restriction transformers
------------------------------------------------------------------------

module Graded.Modality.Morphism.Type-restrictions.Examples where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Unit

open import Graded.Modality
open import Graded.Modality.Instances.Affine
  using (affineModality)
open import Graded.Modality.Instances.Erasure
  using (𝟘; ω)
open import Graded.Modality.Instances.Erasure.Modality
  using (ErasureModality)
open import Graded.Modality.Instances.Linear-or-affine
  using (𝟘; 𝟙; ≤𝟙; ≤ω; linear-or-affine)
open import Graded.Modality.Instances.Linearity
  using (linearityModality)
open import Graded.Modality.Instances.Unit using (UnitModality)
open import Graded.Modality.Instances.Zero-one-many
  using (𝟘; 𝟙; ω; zero-one-many-modality)
open import Graded.Modality.Morphism.Examples
open import Graded.Modality.Morphism.Type-restrictions
import Graded.Modality.Properties
open import Graded.Restrictions

open import Definition.Typed.Restrictions

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.QuantityTranslation

private variable
  𝟙≤𝟘     : Bool
  R R₁ R₂ : Type-restrictions _
  M₁ M₂   : Set _
  𝕄₁ 𝕄₂   : Modality _
  tr tr-Σ : M₁ → M₂

------------------------------------------------------------------------
-- Preserving/reflecting certain type restrictions

-- If tr preserves type restrictions for R₁ and R₂, then it also does
-- this for equal-binder-quantities M₁ R₁ and
-- equal-binder-quantities M₂ R₂.

Are-preserving-type-restrictions-equal-binder-quantities :
  Are-preserving-type-restrictions R₁ R₂ tr tr →
  Are-preserving-type-restrictions
    (equal-binder-quantities R₁)
    (equal-binder-quantities R₂)
    tr tr
Are-preserving-type-restrictions-equal-binder-quantities {tr = tr} r =
  record
    { Unit-preserved = R.Unit-preserved
    ; ΠΣ-preserved   = λ {b = b} → λ where
        (bn , refl) →
            R.ΠΣ-preserved bn
          , tr-BinderMode-one-function _ _ refl b
    }
  where
  module R = Are-preserving-type-restrictions r

-- If tr reflects type restrictions for R₁ and R₂, then it also does
-- this for equal-binder-quantities M₁ R₁ and
-- equal-binder-quantities M₂ R₂, assuming that the function is
-- injective.

Are-reflecting-type-restrictions-equal-binder-quantities :
  (∀ {p q} → tr p ≡ tr q → p ≡ q) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr →
  Are-reflecting-type-restrictions
    (equal-binder-quantities R₁)
    (equal-binder-quantities R₂)
    tr tr
Are-reflecting-type-restrictions-equal-binder-quantities
  {tr = tr} inj r = record
  { Unit-reflected = Unit-reflected
  ; ΠΣ-reflected   =
      λ {b = b} {p = p} {q = q} (bn , eq) →
          ΠΣ-reflected bn
        , inj (
            tr p                     ≡˘⟨ tr-BinderMode-one-function _ _ refl b ⟩
            tr-BinderMode tr tr b p  ≡⟨ eq ⟩
            tr q                     ∎)
  }
  where
  open Are-reflecting-type-restrictions r
  open Tools.Reasoning.PropositionalEquality

-- If the functions tr and tr-Σ preserve certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘, assuming that tr maps a certain zero to a
-- certain zero.

Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘 :
  tr (Modality.𝟘 𝕄₁) ≡ Modality.𝟘 𝕄₂ →
  Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘 𝕄₂ R₂)
    tr tr-Σ
Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘 tr-𝟘 r = record
  { Unit-preserved = Unit-preserved
  ; ΠΣ-preserved   = λ where
      (b , refl) → ΠΣ-preserved b , tr-𝟘
  }
  where
  open Are-preserving-type-restrictions r

-- If the functions tr and tr-Σ reflect certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘, assuming that tr only maps a certain zero
-- to a certain zero.

Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘 :
  (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘 𝕄₂ R₂)
    tr tr-Σ
Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘 tr-𝟘 r = record
  { Unit-reflected = Unit-reflected
  ; ΠΣ-reflected   = λ (b , eq) → ΠΣ-reflected b , tr-𝟘 eq
  }
  where
  open Are-reflecting-type-restrictions r

-- If the functions tr and tr-Σ preserve certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given that certain assumptions hold.

Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω :
  (𝕄₁ : Modality M₁)
  (𝕄₂ : Modality M₂) →
  (Modality.𝟙 𝕄₁ ≢ Modality.𝟘 𝕄₁ →
   tr (Modality.𝟘 𝕄₁) ≡ Modality.𝟘 𝕄₂) →
  (∀ {p} → tr p ≡ Modality.ω 𝕄₂ ⇔ p ≡ Modality.ω 𝕄₁) →
  (∀ {p} → tr-Σ p ≡ Modality.ω 𝕄₂ ⇔ p ≡ Modality.ω 𝕄₁) →
  Are-preserving-type-restrictions R₁ R₂ tr tr-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ R₂)
    tr tr-Σ
Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
  {tr = tr} {tr-Σ = tr-Σ} 𝕄₁ 𝕄₂ tr-𝟘 tr-ω tr-Σ-ω r = record
  { Unit-preserved = Unit-preserved
  ; ΠΣ-preserved   = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-preserved bn , lemma₁ b is-𝟘 , lemma₃ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-preserving-type-restrictions r
  open Graded.Modality.Properties 𝕄₁

  lemma₁ :
    ∀ {p q} b →
    (p ≡ M₁.ω → q ≡ M₁.ω) →
    tr-BinderMode tr tr-Σ b p ≡ M₂.ω → tr q ≡ M₂.ω
  lemma₁ {p = p} {q = q} BMΠ hyp =
    tr p ≡ M₂.ω  →⟨ tr-ω .proj₁ ⟩
    p ≡ M₁.ω     →⟨ hyp ⟩
    q ≡ M₁.ω     →⟨ tr-ω .proj₂ ⟩
    tr q ≡ M₂.ω  □
  lemma₁ {p = p} {q = q} (BMΣ _) hyp =
    tr-Σ p ≡ M₂.ω  →⟨ tr-Σ-ω .proj₁ ⟩
    p ≡ M₁.ω       →⟨ hyp ⟩
    q ≡ M₁.ω       →⟨ tr-ω .proj₂ ⟩
    tr q ≡ M₂.ω    □

  lemma₂ :
    ∀ {p q} →
    (p ≢ M₁.ω → q ≡ M₁.𝟘) →
    p ≢ M₁.ω → tr q ≡ M₂.𝟘
  lemma₂ {p = p} {q = q} hyp p≢ω₁ =
    case hyp p≢ω₁ of λ {
      refl →
    tr-𝟘 (≢→non-trivial p≢ω₁) }

  lemma₃ :
    ∀ {p q} b →
    (p ≢ M₁.ω → q ≡ M₁.𝟘) →
    tr-BinderMode tr tr-Σ b p ≢ M₂.ω → tr q ≡ M₂.𝟘
  lemma₃ {p = p} {q = q} BMΠ hyp =
    tr p ≢ M₂.ω  →⟨ _∘→ tr-ω .proj₂ ⟩
    p ≢ M₁.ω     →⟨ lemma₂ hyp ⟩
    tr q ≡ M₂.𝟘  □
  lemma₃ {p = p} {q = q} (BMΣ _) hyp =
    tr-Σ p ≢ M₂.ω  →⟨ _∘→ tr-Σ-ω .proj₂ ⟩
    p ≢ M₁.ω       →⟨ lemma₂ hyp ⟩
    tr q ≡ M₂.𝟘    □

-- If the functions tr and tr-Σ reflect certain type restrictions,
-- then they also do this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω, given that certain assumptions hold.

Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω :
  (𝕄₁ : Modality M₁)
  (𝕄₂ : Modality M₂) →
  (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) →
  (∀ {p} → tr p ≡ Modality.ω 𝕄₂ ⇔ p ≡ Modality.ω 𝕄₁) →
  (∀ {p} → tr-Σ p ≡ Modality.ω 𝕄₂ ⇔ p ≡ Modality.ω 𝕄₁) →
  Are-reflecting-type-restrictions R₁ R₂ tr tr-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ R₁)
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ R₂)
    tr tr-Σ
Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
  {tr = tr} {tr-Σ = tr-Σ} 𝕄₁ 𝕄₂ tr-𝟘 tr-ω tr-Σ-ω r = record
  { Unit-reflected = Unit-reflected
  ; ΠΣ-reflected   = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-reflected bn , lemma₁ b is-𝟘 , lemma₂ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-reflecting-type-restrictions r

  lemma₁ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σ b p ≡ M₂.ω → tr q ≡ M₂.ω) →
    p ≡ M₁.ω → q ≡ M₁.ω
  lemma₁ {p = p} {q = q} BMΠ hyp =
    p ≡ M₁.ω     →⟨ tr-ω .proj₂ ⟩
    tr p ≡ M₂.ω  →⟨ hyp ⟩
    tr q ≡ M₂.ω  →⟨ tr-ω .proj₁ ⟩
    q ≡ M₁.ω     □
  lemma₁ {p = p} {q = q} (BMΣ _) hyp =
    p ≡ M₁.ω       →⟨ tr-Σ-ω .proj₂ ⟩
    tr-Σ p ≡ M₂.ω  →⟨ hyp ⟩
    tr q ≡ M₂.ω    →⟨ tr-ω .proj₁ ⟩
    q ≡ M₁.ω       □

  lemma₂ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σ b p ≢ M₂.ω → tr q ≡ M₂.𝟘) →
    p ≢ M₁.ω → q ≡ M₁.𝟘
  lemma₂ {p = p} {q = q} BMΠ hyp =
    p ≢ M₁.ω     →⟨ _∘→ tr-ω .proj₁ ⟩
    tr p ≢ M₂.ω  →⟨ hyp ⟩
    tr q ≡ M₂.𝟘  →⟨ tr-𝟘 ⟩
    q ≡ M₁.𝟘     □
  lemma₂ {p = p} {q = q} (BMΣ _) hyp =
    p ≢ M₁.ω       →⟨ _∘→ tr-Σ-ω .proj₁ ⟩
    tr-Σ p ≢ M₂.ω  →⟨ hyp ⟩
    tr q ≡ M₂.𝟘    →⟨ tr-𝟘 ⟩
    q ≡ M₁.𝟘       □

------------------------------------------------------------------------
-- Some lemmas related to equal-binder-quantities and concrete
-- translation functions

-- The functions erasure→zero-one-many and erasure→zero-one-many-Σ do
-- not preserve certain type restrictions obtained using
-- equal-binder-quantities.

¬-erasure→zero-one-many-Σ-preserves-equal-binder-quantities :
  ¬ Are-preserving-type-restrictions
      (equal-binder-quantities no-type-restrictions)
      (equal-binder-quantities R)
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-erasure→zero-one-many-Σ-preserves-equal-binder-quantities r =
  case ΠΣ-preserved {b = BMΣ Σₚ} {p = ω} (_ , refl) .proj₂ of λ ()
  where
  open Are-preserving-type-restrictions r

-- The functions affine→linear-or-affine and affine→linear-or-affine-Σ
-- do not preserve certain type restrictions obtained using
-- equal-binder-quantities.

¬-affine→linear-or-affine-Σ-preserves-equal-binder-quantities :
  ¬ Are-preserving-type-restrictions
      (equal-binder-quantities no-type-restrictions)
      (equal-binder-quantities R)
      affine→linear-or-affine affine→linear-or-affine-Σ
¬-affine→linear-or-affine-Σ-preserves-equal-binder-quantities r =
  case ΠΣ-preserved {b = BMΣ Σₚ} {p = 𝟙} (_ , refl) .proj₂ of λ ()
  where
  open Are-preserving-type-restrictions r

------------------------------------------------------------------------
-- Some lemmas related to second-ΠΣ-quantities-𝟘-or-ω and concrete
-- translation functions

-- If the function unit→erasure preserves certain type restrictions,
-- then it also does this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

unit→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ →
  Are-preserving-type-restrictions
    R₁ R₂ unit→erasure unit→erasure →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (UnitModality v₁ v₁-ok) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (ErasureModality v₂) R₂)
    unit→erasure unit→erasure
unit→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω v₁ v₁-ok v₂ =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (UnitModality v₁ v₁-ok)
    (ErasureModality v₂)
    (λ tt≢tt → ⊥-elim (tt≢tt refl))
    ((λ _ → refl) , (λ _ → refl))
    ((λ _ → refl) , (λ _ → refl))

-- If the function unit→erasure reflects certain type restrictions,
-- then it also does this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₁-ok v₂ →
  Are-reflecting-type-restrictions
    R₁ R₂ unit→erasure unit→erasure →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (UnitModality v₁ v₁-ok) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (ErasureModality v₂) R₂)
    unit→erasure unit→erasure
unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω v₁ v₁-ok v₂ =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (UnitModality v₁ v₁-ok)
    (ErasureModality v₂)
    (λ ())
    ((λ _ → refl) , (λ _ → refl))
    ((λ _ → refl) , (λ _ → refl))

-- If the function erasure→unit preserves certain type restrictions,
-- then it also does this for certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

erasure→unit-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  Are-preserving-type-restrictions
    R₁ R₂ erasure→unit erasure→unit →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (ErasureModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (UnitModality v₂ v₂-ok) R₂)
    erasure→unit erasure→unit
erasure→unit-preserves-second-ΠΣ-quantities-𝟘-or-ω _ _ _ r =
  record
    { Unit-preserved = Unit-preserved
    ; ΠΣ-preserved   = λ (b , _) →
        ΠΣ-preserved b , (λ _ → refl) , (λ _ → refl)
    }
  where
  open Are-preserving-type-restrictions r

-- The function erasure→unit does not reflect certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-erasure→unit-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ v₂-ok →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω (ErasureModality v₁) R₁)
      (second-ΠΣ-quantities-𝟘-or-ω
         (UnitModality v₂ v₂-ok) no-type-restrictions)
      erasure→unit erasure→unit
¬-erasure→unit-reflects-second-ΠΣ-quantities-𝟘-or-ω _ _ _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = 𝟘} {q = ω}
      (_ , (λ _ → refl) , (λ _ → refl))
  of
    λ (_ , _ , eq) →
  case eq (λ ()) of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function erasure→zero-one-many preserves certain type
-- restrictions, then the function preserves certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-preserving-type-restrictions R₁ R₂
    erasure→zero-one-many erasure→zero-one-many →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (ErasureModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (zero-one-many-modality 𝟙≤𝟘 v₂) R₂)
    erasure→zero-one-many erasure→zero-one-many
erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (ErasureModality v₁)
    (zero-one-many-modality _ v₂)
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the function erasure→zero-one-many reflects certain type
-- restrictions, then the function reflects certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-reflecting-type-restrictions R₁ R₂
    erasure→zero-one-many erasure→zero-one-many →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (ErasureModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (zero-one-many-modality 𝟙≤𝟘 v₂) R₂)
    erasure→zero-one-many erasure→zero-one-many
erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (ErasureModality v₁)
    (zero-one-many-modality _ v₂)
    (λ where
       {p = 𝟘} _  → refl
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- The functions erasure→zero-one-many and erasure→zero-one-many-Σ do
-- not preserve certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

¬-erasure→zero-one-many-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω
         (ErasureModality v₁) no-type-restrictions)
      (second-ΠΣ-quantities-𝟘-or-ω (zero-one-many-modality 𝟙≤𝟘 v₂) R₂)
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-erasure→zero-one-many-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω _ _ r =
  case
    ΠΣ-preserved {b = BMΣ Σₚ} {p = ω} {q = ω}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
      .proj₂ .proj₂ (λ ())
  of λ ()
  where
  open Are-preserving-type-restrictions r

-- The functions erasure→zero-one-many and erasure→zero-one-many-Σ do
-- not reflect certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

¬-erasure→zero-one-many-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω (ErasureModality v₁) R₁)
      (second-ΠΣ-quantities-𝟘-or-ω
         (zero-one-many-modality 𝟙≤𝟘 v₂) no-type-restrictions)
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-erasure→zero-one-many-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω _ _ r =
  case
    ΠΣ-reflected {b = BMΣ Σₚ} {p = ω} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Are-reflecting-type-restrictions r

-- The function zero-one-many→erasure does not preserve certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-zero-one-many→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω
         (zero-one-many-modality 𝟙≤𝟘 v₁) no-type-restrictions)
      (second-ΠΣ-quantities-𝟘-or-ω (ErasureModality v₂) R₂)
      zero-one-many→erasure zero-one-many→erasure
¬-zero-one-many→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω _ _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = 𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Are-preserving-type-restrictions r

-- The function zero-one-many→erasure does not reflect certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-zero-one-many→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω (zero-one-many-modality 𝟙≤𝟘 v₁) R)
      (second-ΠΣ-quantities-𝟘-or-ω
         (ErasureModality v₂) no-type-restrictions)
      zero-one-many→erasure zero-one-many→erasure
¬-zero-one-many→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω _ _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function linearity→linear-or-affine preserves certain type
-- restrictions, then the function preserves certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

linearity→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-preserving-type-restrictions R₁ R₂
    linearity→linear-or-affine linearity→linear-or-affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (linearityModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (linear-or-affine v₂) R₂)
    linearity→linear-or-affine linearity→linear-or-affine
linearity→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linearityModality v₁)
    (linear-or-affine v₂)
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the function linearity→linear-or-affine reflects certain type
-- restrictions, then the function reflects certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

linearity→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-reflecting-type-restrictions R₁ R₂
    linearity→linear-or-affine linearity→linear-or-affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (linearityModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (linear-or-affine v₂) R₂)
    linearity→linear-or-affine linearity→linear-or-affine
linearity→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linearityModality v₁)
    (linear-or-affine v₂)
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- The function linear-or-affine→linearity does not preserve certain
-- type restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-linear-or-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω (linear-or-affine v₁)
         no-type-restrictions)
      (second-ΠΣ-quantities-𝟘-or-ω (linearityModality v₂) R₂)
      linear-or-affine→linearity linear-or-affine→linearity
¬-linear-or-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω
  _ _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = ≤𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Are-preserving-type-restrictions r

-- The function linear-or-affine→linearity does not reflect certain
-- type restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-linear-or-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω (linear-or-affine v₁) R)
      (second-ΠΣ-quantities-𝟘-or-ω
         (linearityModality v₂) no-type-restrictions)
      linear-or-affine→linearity linear-or-affine→linearity
¬-linear-or-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω
  _ _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ≤ω} {q = ≤𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function affine→linear-or-affine preserves certain type
-- restrictions, then the function preserves certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-preserving-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (linear-or-affine v₂) R₂)
    affine→linear-or-affine affine→linear-or-affine
affine→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω
  v₁ v₂ =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (affineModality v₁)
    (linear-or-affine v₂)
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the function affine→linear-or-affine reflects certain type
-- restrictions, then the function reflects certain type restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-reflecting-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (linear-or-affine v₂) R₂)
    affine→linear-or-affine affine→linear-or-affine
affine→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (affineModality v₁)
    (linear-or-affine v₂)
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the functions affine→linear-or-affine and
-- affine→linear-or-affine-Σ preserve certain type restrictions, then
-- the functions preserve certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-preserving-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine-Σ →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (linear-or-affine v₂) R₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
affine→linear-or-affine-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (affineModality v₁)
    (linear-or-affine v₂)
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the functions affine→linear-or-affine and
-- affine→linear-or-affine-Σ reflect certain type restrictions, then
-- the functions reflect certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-reflecting-type-restrictions R₁ R₂
    affine→linear-or-affine affine→linear-or-affine-Σ →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (linear-or-affine v₂) R₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
affine→linear-or-affine-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (affineModality v₁)
    (linear-or-affine v₂)
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the function linear-or-affine→affine preserves certain type
-- restrictions, then the function also preserves certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

linear-or-affine→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-preserving-type-restrictions R₁ R₂
    linear-or-affine→affine linear-or-affine→affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (linear-or-affine v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₂) R₂)
    linear-or-affine→affine linear-or-affine→affine
linear-or-affine→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linear-or-affine v₁)
    (affineModality v₂)
    (λ _ → refl)
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))

-- If the function linear-or-affine→affine reflects certain type
-- restrictions, then the function also reflects certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

linear-or-affine→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-reflecting-type-restrictions R₁ R₂
    linear-or-affine→affine linear-or-affine→affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (linear-or-affine v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₂) R₂)
    linear-or-affine→affine linear-or-affine→affine
linear-or-affine→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linear-or-affine v₁)
    (affineModality v₂)
    (λ where
       {p = 𝟘}  _  → refl
       {p = 𝟙}  ()
       {p = ≤𝟙} ()
       {p = ≤ω} ())
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))

-- The function affine→linearity does not preserve certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₁)
         no-type-restrictions)
      (second-ΠΣ-quantities-𝟘-or-ω (linearityModality v₂) R₂)
      affine→linearity affine→linearity
¬-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω _ _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = 𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Are-preserving-type-restrictions r

-- The function affine→linearity does not reflect certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₁) R)
      (second-ΠΣ-quantities-𝟘-or-ω
         (linearityModality v₂) no-type-restrictions)
      affine→linearity affine→linearity
¬-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω _ _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Are-reflecting-type-restrictions r

-- The functions affine→linearity and affine→linearity-Σ do not
-- preserve certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  ¬ Are-preserving-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₁)
         no-type-restrictions)
      (second-ΠΣ-quantities-𝟘-or-ω (linearityModality v₂) R₂)
      affine→linearity affine→linearity-Σ
¬-affine→linearity-Σ-preserves-second-ΠΣ-quantities-𝟘-or-ω _ _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = 𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Are-preserving-type-restrictions r

-- The functions affine→linearity and affine→linearity-Σ do not
-- reflect certain type restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  ¬ Are-reflecting-type-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₁) R)
      (second-ΠΣ-quantities-𝟘-or-ω
         (linearityModality v₂) no-type-restrictions)
      affine→linearity affine→linearity-Σ
¬-affine→linearity-Σ-reflects-second-ΠΣ-quantities-𝟘-or-ω _ _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Are-reflecting-type-restrictions r

-- If the function linearity→affine preserves certain type
-- restrictions, then the function also preserves certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

linearity→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-preserving-type-restrictions R₁ R₂
    linearity→affine linearity→affine →
  Are-preserving-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (linearityModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₂) R₂)
    linearity→affine linearity→affine
linearity→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ =
  Are-preserving-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linearityModality v₁)
    (affineModality v₂)
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- If the function linearity→affine reflects certain type
-- restrictions, then the function also reflects certain type
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

linearity→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ v₁ v₂ →
  Are-reflecting-type-restrictions R₁ R₂
    linearity→affine linearity→affine →
  Are-reflecting-type-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω (linearityModality v₁) R₁)
    (second-ΠΣ-quantities-𝟘-or-ω (affineModality v₂) R₂)
    linearity→affine linearity→affine
linearity→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω v₁ v₂ =
  Are-reflecting-type-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    (linearityModality v₁)
    (affineModality v₂)
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

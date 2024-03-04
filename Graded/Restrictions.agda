------------------------------------------------------------------------
-- Definitions related to type and usage restrictions
------------------------------------------------------------------------

import Graded.Modality

module Graded.Restrictions
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Relation as Dec
open import Tools.Unit

open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions 𝕄

open import Definition.Typed.Restrictions 𝕄
open import Definition.Untyped.NotParametrised

private variable
  TR : Type-restrictions
  UR : Usage-restrictions

-- No type restrictions except that if the modality is trivial, then
-- []-cong is not allowed, and the K rule is allowed if the boolean is
-- true.

no-type-restrictions : Bool → Type-restrictions
no-type-restrictions allowed = λ where
    .Unit-allowed     → λ _ → Lift _ ⊤
    .ΠΣ-allowed       → λ _ _ _ → Lift _ ⊤
    .K-allowed        → Lift _ (T allowed)
    .[]-cong-allowed  → λ _ → ¬ Trivial
    .[]-cong→Erased   → _
    .[]-cong→¬Trivial → idᶠ
  where
  open Type-restrictions

-- No restrictions for prodrec or unitrec, all erased matches are
-- allowed for J and K, Id-erased is inhabited if the first boolean is
-- true, and starˢ is treated as a sink if the second boolean is true.

no-usage-restrictions : Bool → Bool → Usage-restrictions
no-usage-restrictions erased sink = λ where
    .Prodrec-allowed                  → λ _ _ _ _ → Lift _ ⊤
    .Prodrec-allowed-downwards-closed → _
    .Unitrec-allowed                  → λ _ _ _ → Lift _ ⊤
    .Unitrec-allowed-downwards-closed → _
    .starˢ-sink                       → sink
    .Id-erased                        → Lift _ (T erased)
    .Id-erased?                       → Dec.map lift Lift.lower $
                                        T? erased
    .erased-matches-for-J             → λ _ → all
    .erased-matches-for-J-≤ᵉᵐ         → _
    .erased-matches-for-K             → λ _ → all
    .erased-matches-for-K-≤ᵉᵐ         → _
  where
  open Usage-restrictions

-- The function adds the restriction that the two quantities on a Π-
-- or Σ-type have to be equal.

equal-binder-quantities : Type-restrictions → Type-restrictions
equal-binder-quantities R = record R
  { ΠΣ-allowed     = λ b p q → ΠΣ-allowed b p q × p ≡ q
  ; []-cong→Erased = λ ok →
      []-cong→Erased ok .proj₁ , []-cong→Erased ok .proj₂ , refl
  }
  where
  open Type-restrictions R

-- The function adds the restriction that the second quantities
-- associated with Π- and Σ-types are equal to 𝟘.

second-ΠΣ-quantities-𝟘 :
  Type-restrictions → Type-restrictions
second-ΠΣ-quantities-𝟘 R = record R
  { ΠΣ-allowed     = λ b p q → ΠΣ-allowed b p q × q ≡ 𝟘
  ; []-cong→Erased = λ ok →
      []-cong→Erased ok .proj₁ , []-cong→Erased ok .proj₂ , refl
  }
  where
  open Type-restrictions R

-- The function second-ΠΣ-quantities-𝟘-or-ω 𝕄 adds the restriction
-- that if the first quantity associated with a Π- or Σ-type is the ω
-- grade of 𝕄, then the second quantity is also ω, and if the first
-- quantity is not ω, then the second quantity is the 𝟘 of 𝕄.

second-ΠΣ-quantities-𝟘-or-ω :
  Type-restrictions → Type-restrictions
second-ΠΣ-quantities-𝟘-or-ω R = record R
  { ΠΣ-allowed = λ b p q →
      ΠΣ-allowed b p q ×
      (p ≡ ω → q ≡ ω) ×
      (p ≢ ω → q ≡ 𝟘)
  ; []-cong→Erased = λ ok →
        []-cong→Erased ok .proj₁
      , []-cong→Erased ok .proj₂
      , idᶠ
      , λ _ → refl
  }
  where
  open Type-restrictions R

-- A lemma used to define strong-types-restricted and no-strong-types.

strong-types-restricted′ :
  (P : BinderMode → M → Set a) →
  (∀ {s} → s ≢ 𝕤 → P (BMΣ s) 𝟘) →
  Type-restrictions → Type-restrictions
strong-types-restricted′ P hyp R = record R
  { Unit-allowed = λ s →
      Unit-allowed s × s ≢ 𝕤
  ; ΠΣ-allowed = λ b p q →
      ΠΣ-allowed b p q × P b p
  ; []-cong-allowed = λ s →
      []-cong-allowed s × s ≢ 𝕤
  ; []-cong→Erased = λ (ok , s≢𝕤) →
        ([]-cong→Erased ok .proj₁ , s≢𝕤)
      , []-cong→Erased ok .proj₂
      , hyp s≢𝕤
  ; []-cong→¬Trivial =
      []-cong→¬Trivial ∘→ proj₁
  }
  where
  open Type-restrictions R

-- The function strong-types-restricted adds the following
-- restrictions:
--
-- * The strong unit type is not allowed.
-- * If strong Σ-types are allowed for p and q, then p is 𝟙.
-- * []-cong is not allowed for 𝕤.

strong-types-restricted :
  Type-restrictions → Type-restrictions
strong-types-restricted =
  strong-types-restricted′ (λ b p → b ≡ BMΣ 𝕤 → p ≡ 𝟙)
    (λ { hyp refl → ⊥-elim $ hyp refl })

-- The function no-strong-types adds the following restrictions:
--
-- * The strong unit type is not allowed.
-- * Strong Σ-types are not allowed.
-- * []-cong is not allowed for 𝕤.

no-strong-types :
  Type-restrictions → Type-restrictions
no-strong-types =
  strong-types-restricted′ (λ b _ → Lift _ (b ≢ BMΣ 𝕤))
    (λ hyp → lift (λ { refl → ⊥-elim $ hyp refl }))

-- The property of not allowing erased matches.
--
-- "Erased" matches are allowed for trivial modalities. Erased matches
-- are also allowed when the mode is not 𝟙ᵐ, except for []-cong. (Note
-- that a variant of []-cong that works when the mode is not 𝟙ᵐ can be
-- defined without the use of []-cong, see
-- Graded.Box-cong.▸[]-cong-J-𝟘ᵐ.)

No-erased-matches : Type-restrictions → Usage-restrictions → Set a
No-erased-matches TR UR =
  ¬ Trivial →
  (∀ {r p q} → Prodrec-allowed 𝟙ᵐ r p q → r ≢ 𝟘) ×
  (∀ {p q}   → Unitrec-allowed 𝟙ᵐ p q   → p ≢ 𝟘) ×
  (∀ {s} → ¬ ([]-cong-allowed s)) ×
  erased-matches-for-J 𝟙ᵐ ≡ none ×
  erased-matches-for-K 𝟙ᵐ ≡ none
  where
  open Type-restrictions TR
  open Usage-restrictions UR

-- The function adds the restriction that erased matches are not
-- allowed for the given strength.

no-erased-matches-TR : Strength → Type-restrictions → Type-restrictions
no-erased-matches-TR s TR = record TR
  { []-cong-allowed  = λ s′ → []-cong-allowed s′ × s′ ≢ s
  ; []-cong→Erased   = []-cong→Erased ∘→ proj₁
  ; []-cong→¬Trivial = []-cong→¬Trivial ∘→ proj₁
  }
  where
  open Type-restrictions TR

-- The function adds the restriction that erased matches are not
-- allowed for the mode 𝟙ᵐ (for prodrec and unitrec the restriction
-- only applies to non-trivial modalities).

no-erased-matches-UR : Usage-restrictions → Usage-restrictions
no-erased-matches-UR UR = record UR
  { Prodrec-allowed = λ m r p q →
      Prodrec-allowed m r p q ×
      (¬ Trivial → m ≡ 𝟙ᵐ → r ≢ 𝟘)
  ; Prodrec-allowed-downwards-closed =
      Σ.map Prodrec-allowed-downwards-closed (λ _ _ ())
  ; Unitrec-allowed = λ m p q →
      Unitrec-allowed m p q ×
      (¬ Trivial → m ≡ 𝟙ᵐ → p ≢ 𝟘)
  ; Unitrec-allowed-downwards-closed =
      Σ.map Unitrec-allowed-downwards-closed (λ _ _ ())
  ; erased-matches-for-J = λ where
      𝟙ᵐ → none
      𝟘ᵐ → erased-matches-for-J 𝟘ᵐ
  ; erased-matches-for-J-≤ᵉᵐ =
      _
  ; erased-matches-for-K = λ where
      𝟙ᵐ → none
      𝟘ᵐ → erased-matches-for-K 𝟘ᵐ
  ; erased-matches-for-K-≤ᵉᵐ =
      _
  }
  where
  open Usage-restrictions UR

-- Certain restrictions obtained from no-erased-matches-TR and
-- no-erased-matches-UR satisfy No-erased-matches.

No-erased-matches-no-erased-matches :
  ∀ TR UR →
  No-erased-matches
    (no-erased-matches-TR 𝕤 (no-erased-matches-TR 𝕨 TR))
    (no-erased-matches-UR UR)
No-erased-matches-no-erased-matches _ _ 𝟙≢𝟘 =
    (_$ refl) ∘→ (_$ 𝟙≢𝟘) ∘→ proj₂
  , (_$ refl) ∘→ (_$ 𝟙≢𝟘) ∘→ proj₂
  , (λ where
       {s = 𝕤} → (_$ refl) ∘→ proj₂
       {s = 𝕨} → (_$ refl) ∘→ proj₂ ∘→ proj₁)
  , refl
  , refl

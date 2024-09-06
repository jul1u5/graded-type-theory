open import Graded.Modality

module ArrayLang.Heap.Equality.UpToGrades
  {ℓ} {M : Set ℓ}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Agda.Primitive

open import Graded.Context 𝕄
open import Graded.Modality.Properties.Subtraction semiring-with-meet

open import ArrayLang.Syntax 𝕄
open import ArrayLang.Usage 𝕄
open import ArrayLang.Heap 𝕄

open import Tools.Nat
open import Tools.Fin
open import Tools.Product
open import Tools.Function
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private
  variable
    p q : M
    n m : Nat
    Γ Γ′ Δ Δ′ : Con _
    A B C : Type
    𝓐 𝓑 𝓒 : ConItem _
    ρ E E′ : Ren _ _
    x : _ ∋ᶜ _
    o o′ : HeapObject _ _
    H H′ H″ : Heap _

-- Equality of heaps up to grades

data _~ʰ_ : (H H′ : Heap Γ) → Set ℓ where
  ε   : ε ~ʰ ε
  _∙_ : H          ~ʰ H′          → (o : HeapObject Γ 𝓐)
      → H ∙[ p ]ₕ o ~ʰ H′ ∙[ q ]ₕ o

------------------------------------------------------------------------
-- Properties of heap equality

-- Heap equality is reflective

~ʰ-refl : H ~ʰ H
~ʰ-refl {H = ε} = ε
~ʰ-refl {H = H ∙[ p ]ₕ c} = ~ʰ-refl ∙ _

-- Heap equality is symmetric

~ʰ-sym : H ~ʰ H′ → H′ ~ʰ H
~ʰ-sym ε = ε
~ʰ-sym (H~H′ ∙ c) = ~ʰ-sym H~H′ ∙ c

-- Heap equality is transitive

~ʰ-trans : H ~ʰ H′ → H′ ~ʰ H″ → H ~ʰ H″
~ʰ-trans ε ε = ε
~ʰ-trans (H~H′ ∙ c) (H′~H″ ∙ .c) = ~ʰ-trans H~H′ H′~H″ ∙ c

-- Heap lookup without update behaves the same on equal heaps

~ʰ-lookup : H ~ʰ H′ → H ⊢ x ↦ o → H′ ⊢ x ↦ o
~ʰ-lookup (H~H′ ∙ _) (_ , vz[] _) = _ , vz[] p-𝟘≡p
~ʰ-lookup (H~H′ ∙ _) (_ , vs[] d) =
  case ~ʰ-lookup H~H′ (_ , d) of λ {
  (_ , d′) → _ , vs[] d′
  }

-- Equal heaps are equal as substitutions

-- ~ʰ-subst : H ~ʰ H′ → toSubstₕ H ≡ toSubstₕ H′
-- ~ʰ-subst ε = refl
-- ~ʰ-subst (H~H′ ∙ (t , E)) =
--   case ~ʰ-subst H~H′ of λ
--     H≡H′ →
--   cong₂ consSubst H≡H′ (cong (wk E t [_]) H≡H′)

-- An updated heap is equal to the original one (up to grades)

update-~ʰ : H ⊢ x ↦[ p - q ] o ⨾ H′ → H ~ʰ H′
update-~ʰ (vz[] _) = ~ʰ-refl ∙ _
update-~ʰ (vs[] d) = update-~ʰ d ∙ _

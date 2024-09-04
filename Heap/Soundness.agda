
open import Graded.Modality
open import Graded.Usage.Restrictions
open import Heap.Usage.Assumptions
open import Definition.Typed.Restrictions
open import Tools.Relation
open import Tools.Sum hiding (id)

module Heap.Soundness
  {a} {M : Set a} {𝕄 : Modality M}
  {UR : Usage-restrictions 𝕄}
  (UA : UsageAssumptions UR)
  (TR : Type-restrictions 𝕄)
  (open Type-restrictions TR)
  (no-Unitʷ⊎no-η : ¬ Unitʷ-allowed ⊎ ¬ Unitʷ-η)
  where

open UsageAssumptions UA
open Modality 𝕄

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
import Tools.Reasoning.PartialOrder as RPo

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.EqRelInstance TR
open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Fundamental.Reducibility TR
open import Definition.LogicalRelation.Substitution.Introductions.Nat TR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR

open import Heap.Options
open import Heap.Untyped 𝕄 hiding (wkᶜ)
open import Heap.Untyped.Properties 𝕄
open import Heap.Usage 𝕄 UR
open import Heap.Usage.Properties UR type-variant
import Heap.Usage.Reduction UA type-variant (tracking-and-ℕ-fullred-if false) as URᶠ
import Heap.Usage.Reduction UA type-variant (tracking-and-ℕ-fullred-if true) as URᵗ
open import Heap.Termination UA TR no-Unitʷ⊎no-η
open import Heap.Typed TR false
open import Heap.Typed.Reduction TR (tracking-and-ℕ-fullred-if false)
open import Heap.Bisimilarity UR TR
open import Heap.Normalization 𝕄
open import Heap.Reduction 𝕄 (tracking-and-ℕ-fullred-if true)
open import Heap.Reduction.Properties 𝕄 type-variant (tracking-and-ℕ-fullred-if true)
  using (_⇨*_; ++sucₛ-⇒*)
open import Heap.Reduction.Properties 𝕄 type-variant (not-tracking-and-ℕ-fullred-if false)
  using (⇒ₙ*-norm-≡; ⇒ₙ*_)



private variable
  m : Nat
  n t A : Term _
  s : State _ _
  γ δ η : Conₘ _
  Γ : Con Term _
  H : Heap _
  E : Env _ _
  S : Stack _

opaque

  -- All well-typed and well-resourced states of type ℕ reduce to numerals

  redNumeral : ε ⊩ℕ n ∷ℕ → n ≡ norm s → Γ ⊢ₛ s ∷ ℕ → γ ⨾ δ ⨾ η ▸ s
      → ∃₄ λ m n H (E : Env m n) → ∃ λ t → s ⇒* ⟨ H , t , E , ε ⟩ × Numeral t
  redNumeral (ℕₜ _ d n≡n (sucᵣ x)) refl ⊢s ▸s =
    case whBisim (redₜ d , sucₙ) ⊢s ▸s of λ
      (_ , _ , H , t , E , d′ , ≡u , v) →
    case subst-suc {t = wk E t} ≡u of λ {
      (inj₁ (x , ≡x)) →
    case wk-var ≡x of λ {
      (_ , refl , _) →
    case v of λ ()};
      (inj₂ (n′ , ≡suc , ≡n)) →
    case wk-suc ≡suc of λ {
      (n″ , refl , ≡n′) →
    case isNumeral? n″ of λ {
      (yes num) →
    _ , _ , _ , _ , _ , bisim₇* true d′ , sucₙ num ;
      (no ¬num) →
    case ⊢ₛ-⇒* ⊢s d′ of λ
      (_ , _ , _ , _ , ⊢H , ⊢t , ⊢S) →
    case inversion-suc ⊢t of λ
      (⊢n″ , ≡ℕ) →
    case URᶠ.▸-⇒* ▸s d′ of λ
      (_ , _ , _ , ▸H , ▸t , ▸ε , γ≤) →
    case inv-usage-suc ▸t of λ
      (invUsageSuc ▸n″ δ≤)  →
    case redNumeral {s = ⟨ H , n″ , E , ε ⟩} x
          (PE.sym (PE.trans (cong (_[ H ]ₕ) ≡n′) ≡n))
          (_ , ⊢H , ⊢n″ , ε)
          (▸H , ▸n″ , ▸ε , ≤ᶜ-trans γ≤ (+ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)))) of λ
      (_ , _ , H′ , E′ , t′ , d₀ , n) →
    _ , _ , _ , _ , _
      , (bisim₇* true d′ ⇨* ((⇒ₛ (sucₕ ¬num)) ⇨
          (++sucₛ-⇒* {k = 1} d₀ ⇨* ((⇒ₛ (numₕ n)) ⇨ id))))
      , sucₙ n }}}

  redNumeral (ℕₜ _ d n≡n zeroᵣ) refl ⊢s ▸s =
    case whBisim (redₜ d , zeroₙ) ⊢s ▸s of λ
      (_ , _ , H , t , E , d′ , ≡u , v) →
    case subst-zero {t = wk E t} ≡u of λ {
      (inj₁ (x , ≡x)) →
    case wk-var ≡x of λ {
      (_ , refl , w) →
    case v of λ ()} ;
      (inj₂ ≡zero) →
    case wk-zero ≡zero of λ {
      refl →
    _ , _ , _ , _ , _ , bisim₇* true d′ , zeroₙ }}

  redNumeral (ℕₜ _ d n≡n (ne (neNfₜ neK ⊢k k≡k))) n≡ ⊢s ▸s =
    ⊥-elim (noClosedNe neK)

opaque

  -- All well-typed and well-resourced terms of type ℕ reduce to some
  -- numeral and the resulting heap has all grades less than or equal to 𝟘.

  soundness : ε ⊢ t ∷ ℕ → ε ▸ t
            → ∃₂ λ m n → ∃₃ λ H t′ (E : Env m n) →
              initial t ⇒* ⟨ H , t′ , E , ε ⟩ × Numeral t′ × H ≤ʰ 𝟘
  soundness {t} ⊢t ▸t =
    case ▸initial ▸t of λ
      ▸s →
    case ⊩∷ℕ⇔ .proj₁ (reducible-⊩∷ ⊢t) of λ
      [t] →
    case redNumeral [t] (PE.sym (PE.trans (subst-id (wk id t)) (wk-id t)))
           (⊢initial ⊢t) ▸s of λ
      (_ , _ , H , E , t , d , num) →
    case URᵗ.▸-⇒* ▸s d of λ {
      (γ , δ , _ , ▸H , ▸n , ε , γ≤) →
    let open RPo ≤ᶜ-poset in
    _ , _ , _ , _ , _ , d , num
      , 𝟘▸H→H≤𝟘 (subₕ ▸H (begin
          γ                  ≤⟨ γ≤ ⟩
          𝟙 ·ᶜ wkᶜ E δ +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityʳ _ ⟩
          𝟙 ·ᶜ wkᶜ E δ       ≈⟨ ·ᶜ-identityˡ _ ⟩
          wkᶜ E δ            ≤⟨ wk-≤ᶜ E (inv-usage-numeral ▸n num) ⟩
          wkᶜ E 𝟘ᶜ           ≡⟨ wk-𝟘ᶜ E ⟩
          𝟘ᶜ                 ∎ ))}

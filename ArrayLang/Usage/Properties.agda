------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States.
--
-- Note that this module assumes that resource tracking is turned on.
------------------------------------------------------------------------

import Graded.Modality
import Graded.Modality.Properties

open import Tools.PropositionalEquality
open import Tools.Product
open import Tools.Sum hiding (id; sym)

module ArrayLang.Usage.Properties
  {ℓ} {M : Set ℓ}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Modality 𝕄)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄
  (open Graded.Modality.Properties 𝕄)
  (-≡→≡+ : ∀ {p q r} → p - q ≡ r → p ≡ r + q)
  (+≡𝟙 : ∀ {p q} → p + q ≡ 𝟙 → p ≡ 𝟙 × q ≡ 𝟘 ⊎ p ≡ 𝟘 × q ≡ 𝟙)
  (subtraction-ok : Supports-subtraction)
  where

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄

open import ArrayLang.Syntax 𝕄
open import ArrayLang.Usage 𝕄
open import ArrayLang.Heap 𝕄
open import ArrayLang.Heap.Properties 𝕄
open import ArrayLang.Reduction 𝕄

open import Tools.Bool
open import Tools.Relation
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Unit

import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder as RPo
import Tools.Reasoning.PropositionalEquality as RPE

open import Data.Fin using () renaming (fromℕ< to fromNat<; toℕ to toNat)
open import Data.Vec using (Vec; lookup; _[_]≔_; replicate)

private variable
  n m : Nat
  Γ Δ : Con _
  γ δ η : Conₘ _
  H H′ : Heap _
  x : _ ∋ᶜ _
  ρ E E′ : Ren _ _
  A B : Type
  t t′ : _ ⊢ _
  v v′ : _ ⊢ᵥ _
  p p′ q q′ r r′ : M
  s s′ : State _ _ _ _
  S S′ : Stack _ _ _
  o : HeapObject _ _
  e : Elim _ _ _

opaque

  -- The multiplicity of a well-resourced eliminator is not zero
  ▸∣e∣≢𝟘 : γ ▸ᵉ e → ∣ e ∣ᵉ ≢ 𝟘
  ▸∣e∣≢𝟘 (-∘ₑ x) = non-trivial
  ▸∣e∣≢𝟘 ((x ∘ₑ-) p≢𝟘) = p≢𝟘
  ▸∣e∣≢𝟘 sucₑ = non-trivial
  ▸∣e∣≢𝟘 !-ₑ = ω≢𝟘
  ▸∣e∣≢𝟘 ⟨-, x ⟩ₑ = non-trivial
  ▸∣e∣≢𝟘 ⟨ x ,-⟩ₑ = non-trivial
  ▸∣e∣≢𝟘 (let⊗[-]ₑ x) = non-trivial
  ▸∣e∣≢𝟘 (let⋆[-]ₑ x) = non-trivial
  ▸∣e∣≢𝟘 (let![-]ₑ x) = non-trivial
  ▸∣e∣≢𝟘 linearlyₑ = non-trivial
  ▸∣e∣≢𝟘 consumeₑ = non-trivial
  ▸∣e∣≢𝟘 duplicateₑ = non-trivial
  ▸∣e∣≢𝟘 (new₁ₑ x) = non-trivial
  ▸∣e∣≢𝟘 new₂ₑ = non-trivial
  ▸∣e∣≢𝟘 (read₁ₑ x) = non-trivial
  ▸∣e∣≢𝟘 read₂ₑ = non-trivial
  ▸∣e∣≢𝟘 (write₁ₑ x x₁) = ω≢𝟘
  ▸∣e∣≢𝟘 (write₂ₑ x) = non-trivial
  ▸∣e∣≢𝟘 write₃ₑ = non-trivial
  ▸∣e∣≢𝟘 freeₑ = non-trivial

opaque

  -- The multiplicity of a well-resourced stack is either not zero
  -- or contains a non-erased application of emptyrec
  ▸∣S∣≢𝟘 : γ ▸ˢ S
         → ∣ S ∣ ≢ 𝟘
  ▸∣S∣≢𝟘 ε = non-trivial
  ▸∣S∣≢𝟘 {S = e ∙ S} (▸e ∙ ▸S) ∣eS∣≡𝟘 with is-linearlyₑ e
  ... | true  = non-trivial ∣eS∣≡𝟘
  ... | false =
        let ∣S∣≢𝟘 = ▸∣S∣≢𝟘 ▸S
            ∣e∣≢𝟘 = ▸∣e∣≢𝟘 ▸e
        in case zero-product ∣eS∣≡𝟘 of λ where
              (inj₁ ∣S∣≡𝟘) → ∣S∣≢𝟘 ∣S∣≡𝟘
              (inj₂ ∣e∣≡𝟘) → ∣e∣≢𝟘 ∣e∣≡𝟘

renᶜ = renConₘ

infix  60 _⟪_⟫

_⟪_⟫ : {Γ : Con n} (γ : Conₘ n) → (x : Γ ∋ᶜ A) → M
γ ⟪ x ⟫ = γ ⟨ toFin x ⟩

infixl 35 _,_≔′_

_,_≔′_ : (γ : Conₘ n) {Γ : Con n} (x : Γ ∋ᶜ A) (p : M) → Conₘ n
γ , x ≔′ p = γ , toFin x ≔ p

inv-usage-var : {x : Γ ∋ᶜ A} {γ : Conₘ n}
         → γ ▸ (` x) → γ ≤ᶜ (𝟘ᶜ , toFin x ≔ 𝟙)
inv-usage-var var = ≤ᶜ-refl
inv-usage-var (sub γ▸x γ≤γ′) with inv-usage-var γ▸x
... | γ′≤δ = ≤ᶜ-trans γ≤γ′ γ′≤δ

inv-usage-arr : {xs : Vec Nat m}
              → γ ▸ᵒ[ p ] array {Γ = Γ} xs
              → γ ≡ 𝟘ᶜ × p ≡𝟘|𝟙
inv-usage-arr (array p≡𝟘|𝟙) = refl , p≡𝟘|𝟙

inv-usage-lin : γ ▸ᵒ[ p ] lin {Γ = Γ}
              → γ ≡ 𝟘ᶜ × p ≡𝟘|𝟙
inv-usage-lin (lin p≡𝟘∣𝟙) = refl , p≡𝟘∣𝟙

opaque
  -- An inversion lemma for usage of states with variables in head position

  ▸var : ∀ E
       → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
       → γ ≤ᶜ (𝟘ᶜ , renVar E x ≔′ ∣ S ∣) +ᶜ η
  ▸var {γ} {δ} {η} {x} {S} E (▸H , ▸x , ▸S , γ≤) = begin
    γ                                              ≤⟨ γ≤ ⟩
    ∣ S ∣ ·ᶜ renConₘ E δ +ᶜ η                      ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (ren-≤ᶜ E (inv-usage-var ▸x))) ⟩
    ∣ S ∣ ·ᶜ renConₘ E (𝟘ᶜ , x ≔′ 𝟙) +ᶜ η          ≡⟨ cong (λ y → ∣ S ∣ ·ᶜ y +ᶜ η) (ren-,≔ E) ⟩
    ∣ S ∣ ·ᶜ (renConₘ E 𝟘ᶜ , renVar E x ≔′ 𝟙) +ᶜ η ≡⟨ cong (λ y → ∣ S ∣ ·ᶜ (y , renVar E x ≔′ 𝟙) +ᶜ η) (renCon-𝟘ᶜ E) ⟩
    ∣ S ∣ ·ᶜ (𝟘ᶜ , renVar E x ≔′ 𝟙) +ᶜ η           ≡˘⟨ cong (_+ᶜ η) (update-distrib-·ᶜ _ _ _ _) ⟩
    (∣ S ∣ ·ᶜ 𝟘ᶜ , renVar E x ≔′ ∣ S ∣ · 𝟙) +ᶜ η   ≈⟨ +ᶜ-congʳ (update-congˡ (·ᶜ-zeroʳ _)) ⟩
    (𝟘ᶜ , renVar E x ≔′ ∣ S ∣ · 𝟙) +ᶜ η            ≡⟨ cong (λ y → (𝟘ᶜ , renVar E x ≔′ y) +ᶜ η) (·-identityʳ _) ⟩
    (𝟘ᶜ , renVar E x ≔′ ∣ S ∣) +ᶜ η                ∎
    where
    open RPo ≤ᶜ-poset

opaque

  -- A consequence of the above lemma

  ▸var′ : ∀ E
        → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
        → γ ⟪ renVar E x ⟫ ≤ ∣ S ∣ + η ⟪ renVar E x ⟫
  ▸var′ {γ} {δ} {η} {x} {S} E ▸s = begin
    γ ⟪ renVar E x ⟫                                             ≤⟨ lookup-monotone (toFin (renVar E x)) (▸var E ▸s) ⟩
    ((𝟘ᶜ , renVar E x ≔′ ∣ S ∣) +ᶜ η) ⟪ renVar E x ⟫             ≡⟨ lookup-distrib-+ᶜ (𝟘ᶜ , renVar E x ≔′ ∣ S ∣) η (toFin (renVar E x)) ⟩
    (𝟘ᶜ , renVar E x ≔′ ∣ S ∣) ⟪ renVar E x ⟫ + η ⟪ renVar E x ⟫ ≡⟨ +-congʳ (update-lookup 𝟘ᶜ (toFin (renVar E x))) ⟩
    ∣ S ∣ + η ⟪ renVar E x ⟫                                     ∎
    where
    open RPo ≤-poset

opaque

  -- Under some assumptions, lookup always succeeds for well-resourced heaps

  ↦→↦[] : H ⊢ x ↦ o
        → γ ▸ʰ H
        → γ ⟪ x ⟫ ≤ p + q
        → ∃ λ H′ → H ⊢ x ↦[- q ] o ⨾ H′
  ↦→↦[] (_ , vz[] p-q≡r) (▸H ∙ ▸o) p′≤p+q =
    _ , _ , vz[] (subtraction-ok p′≤p+q .proj₂)
  ↦→↦[] {x = vs x} {γ = γ ∙ r} {p} {q} (_ , vs[] x↦) (_∙_ {δ} ▸H _) γ⟨x⟩≤p+q =
    case ↦→↦[] (_ , x↦) ▸H lemma of λ
      (_ , _ , x↦′) →
    _ , _ , vs[] x↦′
    where
    open RPo ≤-poset
    lemma : (γ +ᶜ r ·ᶜ δ) ⟪ x ⟫ ≤ (p + (r ·ᶜ δ) ⟪ x ⟫) + q
    lemma = begin
      (γ +ᶜ r ·ᶜ δ) ⟪ x ⟫      ≡⟨ lookup-distrib-+ᶜ γ _ (toFin x) ⟩
      γ ⟪ x ⟫ + (r ·ᶜ δ) ⟪ x ⟫ ≤⟨ +-monotoneˡ γ⟨x⟩≤p+q ⟩
      (p + q) + (r ·ᶜ δ) ⟪ x ⟫ ≈⟨ +-assoc p q _ ⟩
      p + q + (r ·ᶜ δ) ⟪ x ⟫   ≈⟨ +-congˡ (+-comm q _) ⟩
      p + (r ·ᶜ δ) ⟪ x ⟫ + q   ≈˘⟨ +-assoc p _ q ⟩
      (p + (r ·ᶜ δ) ⟪ x ⟫) + q ∎

opaque

  -- A variant of the above property with usage of states

  ▸↦→↦[] : H ⊢ renVar E x ↦ o
         → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
         → ∃ λ H′ → H ⊢ renVar E x ↦[- ∣ S ∣ ] o ⨾ H′
  ▸↦→↦[] {E} {x} {γ} {η} {S} d ▸s@(▸H , _) =
    ↦→↦[] d ▸H (begin
      γ ⟪ renVar E x ⟫         ≤⟨ ▸var′ E ▸s ⟩
      ∣ S ∣ + η ⟪ renVar E x ⟫ ≡⟨ +-comm _ _ ⟩
      η ⟪ renVar E x ⟫ + ∣ S ∣ ∎)
    where
    open RPo ≤-poset

renᵒ-arr : {xs : Vec Nat m}
         → renᵒ ρ o ≡ array xs
         → o ≡ array xs
renᵒ-arr {o = array _} refl = refl

renᵒ-lin : renᵒ ρ o ≡ lin
         → o ≡ lin
renᵒ-lin {o = lin} refl = refl

opaque
  ▸arr : {xs : Vec Nat m}
       → H ⊢ x ↦[ p - q ] array {Γ = Γ} xs ⨾ H′
       → γ ▸ʰ H
       → p ≡𝟘|𝟙
  ▸arr (vz[ ↑o≡arr ] _) (_∙_ ▸H ▸o) =
    case renᵒ-arr ↑o≡arr of λ { refl →
    case inv-usage-arr ▸o of λ { (refl , p≡𝟘∣𝟙) →
    p≡𝟘∣𝟙
    } }
  ▸arr {x = vs x} {γ = γ ∙ p} (vs[ ↑o≡arr ] x↦) (_∙_ {δ} ▸H ▸o) =
    case renᵒ-arr ↑o≡arr of λ { refl →
    ▸arr x↦ ▸H
    }

opaque
  ▸lin : H ⊢ x ↦[ p - q ] lin ⨾ H′
       → γ ▸ʰ H
       → p ≡𝟘|𝟙
  ▸lin (vz[ ↑o≡lin ] _) (_∙_ ▸H ▸o) =
    case renᵒ-lin ↑o≡lin of λ { refl →
    case inv-usage-lin ▸o of λ { (refl , p≡𝟘∣𝟙) →
    p≡𝟘∣𝟙
    } }
  ▸lin {x = vs x} {γ = γ ∙ p} (vs[ ↑o≡lin ] x↦) (_∙_ {δ} ▸H ▸o) =
    case renᵒ-lin ↑o≡lin of λ { refl →
    ▸lin x↦ ▸H
    }

↦[𝟙-q]→q≡𝟙 : H ⊢ x ↦[ 𝟙 - q ] o ⨾ H′
           → q ≢ 𝟘
           → q ≡ 𝟙
↦[𝟙-q]→q≡𝟙 l q≢𝟘 =
  case ↦[-]→-≡ l of λ { (r , 𝟙-q≡r) →
  case +≡𝟙 (sym (-≡→≡+ 𝟙-q≡r)) of λ where
    (inj₁ (refl , refl)) → ⊥-elim (q≢𝟘 refl)
    (inj₂ (refl , refl)) → refl
  }

▸↦arr→↦[] : {xs : Vec Nat n}
          → H ⊢ renVar E x ↦ array xs
          → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
          → ∃ λ H′ → H ⊢ renVar E x ↦[ 𝟙 - 𝟙 ] array xs ⨾ H′ × ∣ S ∣ ≡ 𝟙
▸↦arr→↦[] {E} d ▸s@(▸H , _ , ▸S , _) =
  case ▸↦→↦[] {E = E} d ▸s of λ { (H′ , p , d′) →
  case ▸arr d′ ▸H of λ where
    (inj₁ refl) →
      case ↦[-]→-≡ d′ of λ { (_ , 𝟘-∣S∣) →
      ⊥-elim (𝟘-q≢p (▸∣S∣≢𝟘 ▸S) 𝟘-∣S∣)
      }
    (inj₂ refl) →
      case ↦[𝟙-q]→q≡𝟙 d′ (▸∣S∣≢𝟘 ▸S) of λ { ∣S∣≡𝟙 →
      H′ , subst (_ ⊢ _ ↦[ _ -_] _ ⨾ _) ∣S∣≡𝟙 d′ , ∣S∣≡𝟙
      }
  }

▸↦lin→↦[] : H ⊢ renVar E x ↦ lin
          → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
          → ∃ λ H′ → H ⊢ renVar E x ↦[ 𝟙 - 𝟙 ] lin ⨾ H′ × ∣ S ∣ ≡ 𝟙
▸↦lin→↦[] {E} d ▸s@(▸H , _ , ▸S , _) =
  case ▸↦→↦[] {E = E} d ▸s of λ { (H′ , p , d′) →
  case ▸lin d′ ▸H of λ where
    (inj₁ refl) →
      case ↦[-]→-≡ d′ of λ where
        (_ , 𝟘-∣S∣) → ⊥-elim (𝟘-q≢p (▸∣S∣≢𝟘 ▸S) 𝟘-∣S∣)
    (inj₂ refl) →
      case ↦[𝟙-q]→q≡𝟙 d′ (▸∣S∣≢𝟘 ▸S) of λ { ∣S∣≡𝟙 →
      H′ , subst (_ ⊢ _ ↦[ _ -_] _ ⨾ _) ∣S∣≡𝟙 d′ , ∣S∣≡𝟙
      }
  }

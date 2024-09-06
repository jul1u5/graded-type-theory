open import Graded.Modality

module ArrayLang.Heap.Properties
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

open import Function.Base using (_∋_)
open import Data.Product using (Σ-syntax)
open import Data.Vec using (Vec; _[_]≔_)

private
  variable
    p p′ q r : M
    n m : Nat
    Γ Γ′ Δ Δ′ Θ Θ′ : Con _
    A B C D : Type
    𝓐 𝓑 𝓒 𝓓 : ConItem _
    ρ σ E E′ : Ren _ _
    t t′ u u′ : _ ⊢ _
    v v′ v₁ v₁′ v₂ v₂′ v₃ v₃′ : _ ⊢ᵥ _
    x : _ ∋ᶜ _
    o o′ : HeapObject _ _
    H H′ H″ Hᵢ Hₒ : Heap _
    S S′ : Stack _ _ _

ren⦅⦆≡⦅ren⦆ : (v : Γ ⊢ᵥ A)
          → ren ρ ⦅ v ⦆ᵛ ≡ ⦅ renᵛ ρ v ⦆ᵛ
ren⦅⦆≡⦅ren⦆ (_ , lam p x)               = refl
ren⦅⦆≡⦅ren⦆ (_ , zero)                  = refl
ren⦅⦆≡⦅ren⦆ (suc t , suc v)             = cong suc (ren⦅⦆≡⦅ren⦆ (t , v))
ren⦅⦆≡⦅ren⦆ (_ , star)                  = refl
ren⦅⦆≡⦅ren⦆ (! t , ! v)                 = cong !_ (ren⦅⦆≡⦅ren⦆ (t , v))
ren⦅⦆≡⦅ren⦆ (⟨ t₁ , t₂ ⟩ , ⟨ v₁ , v₂ ⟩) = cong₂ ⟨_,_⟩ (ren⦅⦆≡⦅ren⦆ (t₁ , v₁)) (ren⦅⦆≡⦅ren⦆ (t₂ , v₂))
ren⦅⦆≡⦅ren⦆ (_ , ref x)                 = refl


-- Equality of eliminators and stacks via a weakening

ren1ˢ-interchange : {𝓐 : ConItem C}
                   {Γ : Con n} {Δ : Con m}
                   (S : Stack Δ A B)
                   (ρ : Ren Γ Δ)
                 → ren1ˢ 𝓐 (renˢ ρ S) ≡ renˢ (liftRen ρ) (ren1ˢ 𝓐 S)
ren1ˢ-interchange = {!!}

------------------------------------------------------------------------
-- Properties of the lookup relations

-- Variable lookup is deterministic.

lookup-det : {H : Heap Γ} {o : HeapObject Γ 𝓐} {o′ : HeapObject Γ 𝓐}
           → H ⊢ x ↦[ p - r ] o  ⨾ H′
           → H ⊢ x ↦[ p′ - r ] o′ ⨾ H″
           → p ≡ p′ × o ≡ o′ × H′ ≡ H″
lookup-det (vz[] p-𝟙≡q) (vz[] p-𝟙≡q′) =
  case -≡-functional p-𝟙≡q p-𝟙≡q′ of λ {
    refl →
  refl , refl , refl }
lookup-det (vs[] x) (vs[] y) =
  case lookup-det x y of λ {
    (refl , refl , refl) →
  refl , refl , refl }

lookup-det′ : {H : Heap Γ} {o : HeapObject Γ 𝓐} {o′ : HeapObject Γ 𝓐}
           → H ⊢ x ↦ o
           → H ⊢ x ↦ o′
           → o ≡ o′
lookup-det′ (_ , vz[] _) (_ , vz[] _) = refl
lookup-det′ (_ , vs[] d) (_ , vs[] d′) =
  case lookup-det′ (_ , d) (_ , d′) of λ {
    refl →
  refl }

-- If heap lookup with update succeeds lookup without heap update
-- succeeds with the same result.

↦[]→↦ : H ⊢ x ↦[- q ] o ⨾ H′ → H ⊢ x ↦ o
↦[]→↦ (_ , vz[] _) = _ , vz[] p-𝟘≡p
↦[]→↦ (_ , vs[] l) =
  let (_ , l) = ↦[]→↦ (_ , l)
   in _ , vs[] l

-- Lookup without heap update always succeeds

lookup′ : (H : Heap Γ) (x : Γ ∋ᶜ 𝓐)
        → ∃ λ (o : HeapObject Γ 𝓐) → H ⊢ x ↦ o
lookup′ (H ∙[ _ ]ₕ o) vz      = ren1ᵒ o , _ , vz[] p-𝟘≡p
lookup′ (H ∙[ _ ]ₕ _) (vs x) =
  let (o , _ , d) = lookup′ H x
   in ren1ᵒ o , _ , vs[] d

vs↦ : {Hᵢ Hₒ : Heap (Γ ∙ 𝓑)}
    → Hᵢ ⊢ vs x ↦[ p - q ] o ⨾ Hₒ
    → ∃₅ λ Hᵢ′ o′ Hₒ′ p′ o″
        → Hᵢ′ ∙[ p′ ]ₕ o″ ≡ Hᵢ
        × ren1ᵒ o′ ≡ o
        × Hₒ′ ∙[ p′ ]ₕ o″ ≡ Hₒ
        × Hᵢ′ ⊢ x ↦[ p - q ] o′ ⨾ Hₒ′
vs↦ (vs[] l) = _ , _ , _ , _ , _ , refl , refl , refl , l

renᵒ-id : (o : HeapObject Γ 𝓐) → renᵒ idRen o ≡ o
renᵒ-id (value v E) = cong (value v) (•-identityˡ E)
renᵒ-id (array _)   = refl
renᵒ-id lin         = refl
renᵒ-id ↯           = refl

renᵒ-• : (ρ : Ren Γ Δ) (σ : Ren Δ Θ)
       → {o : HeapObject Θ 𝓐}
       → renᵒ ρ (renᵒ σ o) ≡ renᵒ (ρ • σ) o
renᵒ-• ρ σ {o = value v E} = cong (value v) (•-assoc ρ σ E)
renᵒ-• ρ σ {o = array xs}  = refl
renᵒ-• ρ σ {o = lin}       = refl
renᵒ-• ρ σ {o = ↯}         = refl

renᵒ-value : renᵒ ρ o ≡ value v E
           → ∃ λ E′ → o ≡ value v E′ × ρ • E′ ≡ E
renᵒ-value {o = value _ _} refl = _ , refl , refl

renᵒ→renᵒ-remap : (ρ : Ren Γ Δ)
                → (x : Δ ∋ᶜ 𝓑)
                → {o  : HeapObject Δ 𝓐}
                → {o′ : HeapObject Γ 𝓐}
                → renᵒ ρ o ≡ o′
                → renᵒ (remapRen x ρ) o ≡ ren1ᵒ o′
renᵒ→renᵒ-remap ρ x {o = value v E} refl = cong (value v) {!!}
renᵒ→renᵒ-remap ρ x {o = array xs} refl = refl
renᵒ→renᵒ-remap ρ x {o = lin} refl = refl
renᵒ→renᵒ-remap ρ x {o = ↯} refl = refl

value-inj : ∀ {n m m′} {Γ : Con n} {Δ : Con m} {Δ′ : Con m′}
            {v : Δ ⊢ᵥ A} {v′ : Δ′ ⊢ᵥ A} →
            {E : Ren Γ Δ} {E′ : Ren Γ Δ′} →
            value v E ≡ value v′ E′ →
            Σ (m ≡ m′) λ { refl →
            Σ (Δ ≡ Δ′) λ { refl →
              (E ≡ E′) ×
              (v ≡ v′)
            }}
value-inj {v} {v′} refl = refl , refl , refl , refl

renᵒ-comp : (ρ : Ren Γ Δ) (σ : Ren Δ Θ) (o : HeapObject Θ 𝓐)
         → renᵒ ρ (renᵒ σ o) ≡ renᵒ (ρ • σ) o
renᵒ-comp ρ σ (value x E) = cong (value x) (•-assoc ρ σ E)
renᵒ-comp ρ σ (array x) = refl
renᵒ-comp ρ σ lin = refl
renᵒ-comp ρ σ ↯ = refl

renᵒ-inj : (ρ : Ren Γ Δ)
         → (o o′ : HeapObject Δ 𝓐)
         → renᵒ ρ o ≡ renᵒ ρ o′
         → o ≡ o′
renᵒ-inj ρ (value v E) (value v′ E′) ≡    =
  case value-inj ≡ of λ { (refl , refl , ρ•E≡ρ•E′ , refl) →
  case •-injʳ _ _ _ ρ•E≡ρ•E′ of λ { refl →
  refl
  }
  }
renᵒ-inj ρ (array xs) (array .xs)    refl = refl
renᵒ-inj ρ lin         lin           _    = refl
renᵒ-inj ρ ↯           ↯             _    = refl

renᵒ-interchange : (ρ : Ren Γ Δ) (o : HeapObject Δ 𝓐)
                 → ren1ᵒ {𝓑 = 𝓑} (renᵒ ρ o) ≡ renᵒ (liftRen ρ) (ren1ᵒ o)
renᵒ-interchange = {!!}

-∘ₑ≡ : ren ρ u ≡ ren σ u′
     → (Elim _ (_ [ p ]⇒ _) B ∋ (-∘ₑ u) ρ) ≡ (-∘ₑ u′) σ
-∘ₑ≡ {u = ` x} p = case ren-var (sym p) of λ { (x′ , refl , p) → {!p!} }
-∘ₑ≡ {u = lam p u} = {!!}
-∘ₑ≡ {u = u ∘ u₁} = {!!}
-∘ₑ≡ {u = zero} = {!!}
-∘ₑ≡ {u = suc u} = {!!}
-∘ₑ≡ {u = star} = {!!}
-∘ₑ≡ {u = let⋆[ u ] u₁} = {!!}
-∘ₑ≡ {u = ! u} = {!!}
-∘ₑ≡ {u = let![ u ] u₁} = {!!}
-∘ₑ≡ {u = ⟨ u , u₁ ⟩} = {!!}
-∘ₑ≡ {u = let⊗[ u ] u₁} = {!!}
-∘ₑ≡ {u = linearly u} = {!!}
-∘ₑ≡ {u = consume u} = {!!}
-∘ₑ≡ {u = duplicate u} = {!!}
-∘ₑ≡ {u = new u u₁} = {!!}
-∘ₑ≡ {u = read u u₁} = {!!}
-∘ₑ≡ {u = write u u₁ u₂} = {!!}
-∘ₑ≡ {u = free u} = {!!}

-- renᵒ-inj : {o o′ : HeapObject Γ 𝓐} →
--           renᵒ ρ o ≡ renᵒ ρ o′ →
--           o ≡ o′
-- renᵒ-inj {o = value v E} {value v′ E′} vρE≡v′ρE′ with value-inj vρE≡v′ρE′
-- ... | refl , refl , ρ•E≡ρ•E′ , refl = cong (value v) (•-inj ρ•E≡ρ•E′)
-- renᵒ-inj {o = array xs}  {array .xs}   refl = refl
-- renᵒ-inj {o = lin}       {lin}         refl = refl
-- renᵒ-inj {o = ↯}         {↯}           refl = refl

renᵒ-array : {xs : Vec Nat n}
           → renᵒ ρ o ≡ array xs
           → o ≡ array xs
renᵒ-array {o = array _} refl = refl

lookup→write : {Γ : Con n} {H H′ : Heap Γ} {x : Γ ∋ᶜ ref}
             → ∀ {size} → {xs : Vec Nat size}
             → H ⊢ x ↦[ 𝟙 - 𝟙 ] array xs ⨾ H′
             → (i : Fin size) (v : Nat)
             → ∃ λ H″ → H ⊢ x ≔ (xs [ i ]≔ v) ⨾ H″
lookup→write {H = H ∙[ p ]ₕ o} {x = vz} (vz[ ren-o≡array ] p-q≡r) i v =
  case renᵒ-array ren-o≡array of λ { refl →
  H ∙[ p ]ₕ array (_ [ i ]≔ v) , vz
  }
lookup→write {H = H ∙[ p ]ₕ o′} {x = vs x} (vs[ ren-o≡array ] l ) i v =
  case renᵒ-array ren-o≡array of λ { refl →
  case lookup→write l i v of λ { (H′ , u) →
  H′ ∙[ p ]ₕ o′ , vs u
  }
  }

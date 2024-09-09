------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States.
--
-- Note that this module assumes that resource tracking is turned on.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions

open import Tools.Bool
open import Tools.Relation

module ArrayLang.Usage.Properties
  {ℓ} {M : Set ℓ} (𝕄 : Modality M)
  (open Modality 𝕄)
  where

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄

open import ArrayLang.Syntax 𝕄
open import ArrayLang.Usage 𝕄
open import ArrayLang.Heap 𝕄
open import ArrayLang.Heap.Properties 𝕄
open import ArrayLang.Reduction 𝕄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum hiding (id; sym)
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
  E E′ : Ren _ _
  A B : Type
  t t′ : _ ⊢ _
  v v′ : _ ⊢ᵥ _
  p p′ q q′ r r′ : M
  s s′ : State _ _ _ _
  S S′ : Stack _ _ _
  o : HeapObject _ _

inv-▸var : {x : Γ ∋ᶜ A} {γ : Conₘ n}
              → γ ▸ (` x) → γ ≤ᶜ (𝟘ᶜ , toFin x ≔ 𝟙)
inv-▸var var = ≤ᶜ-refl
inv-▸var (sub γ▸x γ≤γ′) with inv-▸var γ▸x
... | γ′≤δ = ≤ᶜ-trans γ≤γ′ γ′≤δ

inv-▸ᵒarr : {o : HeapObject Γ Arr}
          → γ ▸ᵒ[ p ] o
          → γ ≡ 𝟘ᶜ × (p ≡ 𝟘 ⊎ p ≡ 𝟙)
inv-▸ᵒarr array𝟘 = refl , inj₁ refl
inv-▸ᵒarr array𝟙 = refl , inj₂ refl

inv-▸ᵒlin : {o : HeapObject Γ Lin}
          → γ ▸ᵒ[ p ] o
          → γ ≡ 𝟘ᶜ × (p ≡ 𝟘 ⊎ p ≡ 𝟙)
inv-▸ᵒlin lin𝟘 = refl , inj₁ refl
inv-▸ᵒlin lin𝟙 = refl , inj₂ refl

inv-▸ʰarr : {H : Heap Γ}
          → (x : Γ ∋ᶜ Arr)
          → γ ▸ʰ H
          → (γ ⟨ toFin x ⟩ ≡ 𝟘 ⊎ γ ⟨ toFin x ⟩ ≡ 𝟙)
inv-▸ʰarr vz (_∙_ ▸H ▸o) with inv-▸ᵒarr ▸o
... | refl , p≡𝟘∨𝟙 = p≡𝟘∨𝟙 
inv-▸ʰarr {γ} (vs x) (▸H ∙ ▸o) with inv-▸ʰarr x ▸H
... | inj₁ p≡𝟘 = {!!}
... | inj₂ p≡𝟙 = {!!}

infix  60 _⟪_⟫

_⟪_⟫ : {Γ : Con n} (γ : Conₘ n) → (x : Γ ∋ᶜ A) → M
γ ⟪ x ⟫ = γ ⟨ toFin x ⟩

module _ (subtraction-ok : Supports-subtraction) where

  -- In a well-resorced heap, lookup of q copies succeeds for pointers whose
  -- associated grade is at most p + q for some p.

  opaque

    ▸H→y↦ : {Γ : Con n} {H : Heap Γ} {x : Γ ∋ᶜ A}
          → γ ▸ʰ H
          → γ ⟪ x ⟫ ≤ p + q
          → ∃₂ λ (o : HeapObject Γ A) H′ → H ⊢ x ↦[- q ] o ⨾ H′
    ▸H→y↦ {p = p} {q} {x = vz} (_∙_ {p = p′} ▸H _) p′≤p+q =
      _ , _ , p′ , vz[] (subtraction-ok p′≤p+q .proj₂)
    ▸H→y↦ {n = 1+ n} {γ = γ ∙ r} {p = p} {q} {x = vs x} (_∙_ {δ} ▸H _) γ⟨i⟩≤p+q =
      case ▸H→y↦ {x = x} ▸H lemma of λ
        (_ , _ , _ , d) →
      _ , _ , _ , vs[] d
      where
        open RPo ≤-poset
        lemma : (γ +ᶜ r ·ᶜ δ) ⟪ x ⟫ ≤ (p + (r ·ᶜ δ) ⟪ x ⟫) + q
        lemma = begin
          (γ +ᶜ r ·ᶜ δ) ⟪ x ⟫      ≡⟨ lookup-distrib-+ᶜ γ _ (toFin x) ⟩
          γ ⟪ x ⟫ + (r ·ᶜ δ) ⟪ x ⟫ ≤⟨ +-monotoneˡ γ⟨i⟩≤p+q ⟩
          (p + q) + (r ·ᶜ δ) ⟪ x ⟫ ≈⟨ +-assoc p q _ ⟩
          p + q + (r ·ᶜ δ) ⟪ x ⟫   ≈⟨ +-congˡ (+-comm q _) ⟩
          p + (r ·ᶜ δ) ⟪ x ⟫ + q   ≈˘⟨ +-assoc p _ q ⟩
          (p + (r ·ᶜ δ) ⟪ x ⟫) + q ∎

  opaque

    -- A variant of the above property with usage of states

    ▸s→y↦ : {Γ : Con n} {Δ : Con m} {E : Ren Γ Δ}
          → {H : Heap Γ} {x : Δ ∋ᶜ A} {S : Stack Γ A B}
          → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
          → ∃₂ λ (o : HeapObject Γ A) H′ → H ⊢ renVar E x ↦[- ∣ S ∣ ] o ⨾ H′
    ▸s→y↦ {n} {m} {γ} {δ} {η} {E} {x} {S} (▸H , ▸t , ▸S , γ≈) =
      ▸H→y↦ ▸H lemma
      where
      open RPo ≤-poset
      i′ : Fin n
      i′ = toFin (renVar E x)
      i : Fin m
      i  = toFin x
      lemma′ : (∣ S ∣ ·ᶜ renConₘ E δ) ⟨ i′ ⟩ ≤ ∣ S ∣
      lemma′ = begin
        (∣ S ∣ ·ᶜ renConₘ E δ) ⟨ i′ ⟩ ≈⟨ lookup-distrib-·ᶜ (renConₘ E δ) ∣ S ∣ i′ ⟩
        ∣ S ∣ · renConₘ E δ ⟨ i′ ⟩    ≡⟨ cong (∣ S ∣ ·_) (ren-⟨⟩ _ E) ⟩
        ∣ S ∣ · δ ⟨ i ⟩               ≤⟨ ·-monotoneʳ (lookup-monotone i (inv-▸var ▸t)) ⟩
        ∣ S ∣ · (𝟘ᶜ , i ≔ 𝟙) ⟨ i ⟩    ≡⟨ cong (∣ S ∣ ·_) (update-lookup 𝟘ᶜ i) ⟩
        ∣ S ∣ · 𝟙                     ≈⟨ ·-identityʳ _ ⟩
        ∣ S ∣                         ∎
      lemma : γ ⟨ i′ ⟩ ≤ η ⟨ i′ ⟩ + ∣ S ∣
      lemma = begin
        γ ⟨ i′ ⟩                                 ≈⟨ {! lookup-monotone i′ γ≈ !} ⟩
        (∣ S ∣ ·ᶜ renConₘ E δ +ᶜ η) ⟨ i′ ⟩       ≡⟨ lookup-distrib-+ᶜ (∣ S ∣ ·ᶜ renConₘ E δ) η i′ ⟩
        (∣ S ∣ ·ᶜ renConₘ E δ) ⟨ i′ ⟩ + η ⟨ i′ ⟩ ≤⟨ +-monotoneˡ lemma′ ⟩
        ∣ S ∣ + η ⟨ i′ ⟩                         ≈⟨ +-comm _ _ ⟩
        η ⟨ i′ ⟩ + ∣ S ∣                         ∎

  opaque
    ▸H→a↦ : {Γ : Con n} {H : Heap Γ} {x : Γ ∋ᶜ Arr}
          → γ ▸ʰ H
          → γ ⟪ x ⟫ ≡ 𝟙
          → ∃₂ λ (o : HeapObject Γ Arr) H′ → H ⊢ x ↦[ 𝟙 - 𝟙 ] o ⨾ H′
    ▸H→a↦ {x = vz} (_∙_ {p} ▸H _) refl =
      _ , _ , vz[] (subtraction-ok (≤-reflexive (sym (+-identityˡ 𝟙))) .proj₂)
    ▸H→a↦ {n = 1+ n} {γ = γ ∙ r} {x = vs x} (_∙_ {p} {δ} ▸H _) γ⟨i⟩≤p+q =
      case ▸H→a↦ {x = x} ▸H lemma of λ
        (_ , _ , d) →
      _ , _ , vs[] d
      where
        -- open RPo ≤-poset
        lemma : (γ +ᶜ r ·ᶜ δ) ⟪ x ⟫ ≡ 𝟙
        lemma = {!   !} -- begin
          -- (γ +ᶜ r ·ᶜ δ) ⟪ x ⟫      ≡⟨ lookup-distrib-+ᶜ γ _ (toFin x) ⟩
          -- γ ⟪ x ⟫ + (r ·ᶜ δ) ⟪ x ⟫ ≤⟨ {! +-monotoneˡ γ⟨i⟩≤p+q !} ⟩
          -- (p + q) + (r ·ᶜ δ) ⟪ x ⟫ ≈⟨ +-assoc p q _ ⟩
          -- p + q + (r ·ᶜ δ) ⟪ x ⟫   ≈⟨ +-congˡ (+-comm q _) ⟩
          -- p + (r ·ᶜ δ) ⟪ x ⟫ + q   ≈˘⟨ +-assoc p _ q ⟩
          -- (p + (r ·ᶜ δ) ⟪ x ⟫) + q ≈⟨ ? ⟩
          -- {!   !} ∎

  opaque
    ▸s→a↦ : {Γ : Con n} {Δ : Con m} {E : Ren Γ Δ}
          → {H : Heap Γ} {a : Δ ∋ᶜ Arr} {S : Stack Γ Arr B}
          → γ ⨾ δ ⨾ η ▸ ⟪ H , ` a , E , S ⟫
          → ∃₂ λ (o : HeapObject Γ Arr) H′ → H ⊢ renVar E a ↦[ 𝟙 - 𝟙 ] o ⨾ H′
    ▸s→a↦ {n} {m} {γ} {δ} {η} {E} {a} {S} (▸H , ▸t , ▸S , γ≤) =
      ▸H→a↦ ▸H lemma
      where
      open RPo ≤-poset
      i′ : Fin n
      i′ = toFin (renVar E a)
      i : Fin m
      i  = toFin a
      -- lemma′ : (∣ S ∣ ·ᶜ renConₘ E δ) ⟨ i′ ⟩ ≤ ∣ S ∣
      -- lemma′ = begin
      --   (∣ S ∣ ·ᶜ renConₘ E δ) ⟨ i′ ⟩ ≈⟨ lookup-distrib-·ᶜ (renConₘ E δ) ∣ S ∣ i′ ⟩
      --   ∣ S ∣ · renConₘ E δ ⟨ i′ ⟩    ≡⟨ cong (∣ S ∣ ·_) (ren-⟨⟩ _ E) ⟩
      --   ∣ S ∣ · δ ⟨ i ⟩               ≤⟨ ·-monotoneʳ (lookup-monotone i (inv-usage-var ▸t)) ⟩
      --   ∣ S ∣ · (𝟘ᶜ , i ≔ 𝟙) ⟨ i ⟩    ≡⟨ cong (∣ S ∣ ·_) (update-lookup 𝟘ᶜ i) ⟩
      --   ∣ S ∣ · 𝟙                     ≈⟨ ·-identityʳ _ ⟩
      --   ∣ S ∣                         ∎
      lemma : γ ⟨ i′ ⟩ ≡ 𝟙
      lemma = {!   !} -- begin
        -- γ ⟨ i′ ⟩                                 ≤⟨ lookup-monotone i′ γ≤ ⟩
        -- (∣ S ∣ ·ᶜ renConₘ E δ +ᶜ η) ⟨ i′ ⟩       ≡⟨ lookup-distrib-+ᶜ (∣ S ∣ ·ᶜ renConₘ E δ) η i′ ⟩
        -- (∣ S ∣ ·ᶜ renConₘ E δ) ⟨ i′ ⟩ + η ⟨ i′ ⟩ ≤⟨ +-monotoneˡ lemma′ ⟩
        -- ∣ S ∣ + η ⟨ i′ ⟩                         ≈⟨ +-comm _ _ ⟩
        -- η ⟨ i′ ⟩ + ∣ S ∣                         ∎

  -- In a well-resourced state, lookup with update succeeds and has the same
  -- result as lookup without update

  ▸↦→↦[] : H ⊢ renVar E x ↦ o
         → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
         → ∃ λ H′ → H ⊢ renVar E x ↦[- ∣ S ∣ ] o ⨾ H′
  ▸↦→↦[] {E} d ▸s =
    case ▸s→y↦ {E = E} ▸s of λ
      (_ , _ , d′) →
    case lookup-det′ d (↦[]→↦ d′) of λ {
      refl →
    _ , d′ }

  ▸a↦→a↦[] : {S : Stack Γ Arr B}
             {xs : Vec Nat n}
           → H ⊢ renVar E x ↦ array xs
           → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
           → ∃ λ H′ → H ⊢ renVar E x ↦[ 𝟙 - 𝟙 ] array xs ⨾ H′
  ▸a↦→a↦[] {E} d ▸s =
    case ▸s→a↦ {E = E} ▸s of λ
      (_ , _ , d′) →
    case lookup-det′ d (↦[]→↦ (𝟙 , d′)) of λ {
      refl →
    _ , d′ }

  ▸S,Arr→∣S∣≡𝟙 : (S : Stack Γ Arr B)
               → η ▸ˢ S
               → ∣ S ∣ ≡ 𝟙
  ▸S,Arr→∣S∣≡𝟙 ε ▸S = refl
  ▸S,Arr→∣S∣≡𝟙 (e ∙ S) ▸S = {!   !}

  ▸↦lin→↦[]lin : H ⊢ renVar E x ↦ lin
               → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
               → ∃ λ H′ → H ⊢ renVar E x ↦[ 𝟙 - 𝟙 ] lin ⨾ H′
  ▸↦lin→↦[]lin {E} d ▸s = {!   !}
    -- case ▸s→a↦ {E = E} ▸s of λ
    --   (_ , _ , d′) →
    -- case lookup-det′ d (↦[]→↦ (𝟙 , d′)) of λ {
    --   refl →
    -- _ , d′ }

  -- ▸ref↦→↦[] : H ⊢ renVar E a ↦ o
  --        → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
  --        → ∃ λ H′ → H ⊢ renVar E x ↦[ 𝟙 - ∣ S ∣ ] o ⨾ H′
  -- ▸ref↦→↦[] {E} d ▸s =
  --   case ▸s→y↦ {E = E} ▸s of λ
  --     (_ , _ , d′) →
  --   case lookup-det′ d (↦[]→↦ d′) of λ {
  --     refl →
  --   _ , d′ }

  ▸linearly→↦[]
    : H ⊢ x ↦ lin
    → γ ⨾ δ ⨾ η ▸ ⟪ H , t , E , linearlyₑ x ∙ S ⟫
    → H ⊢ x ↦[ 𝟘 ] o
  ▸linearly→↦[] d ▸s = {!!}
    -- case ▸linearly→y↦ {! ▸s !} of λ
    --   d′ →
    -- case lookup-det′ d (↦[]→↦ {! d′ !}) of λ {
    --   refl →
    -- _ , d′ }

  -- ▸write↦→↦[]
  --   : {x : Γ ∋ᶜ Arr} {i : Fin n} {v : Nat} {xs : Vec Nat n}
  --   → H ⊢ wkVar E x ↦ o → γ ⨾ δ ⨾ η ▸ ⟪ H  , ` x , E , write₃ₑ (num (toNat i)) (num v) E ∙ S ⟫
  --   → ∃ λ H′ → H ⊢ wkVar E x ↦[ ∣ S ∣ ] o ⨾ H′
  -- ▸write↦→↦[] d ▸s =
  --   case {! ▸s !} of λ
  --     (_ , _ , d′) →
  --   case lookup-det′ d (↦[]→↦ {! d′ !}) of λ {
  --     refl →
  --   _ , d′ }

a↦→∣S∣≡𝟙 : {xs : Vec Nat n}
         → H ⊢ x ↦ array xs
         → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
         → ∣ S ∣ ≡ 𝟙
a↦→∣S∣≡𝟙 {S = ε} l ▸s = {!   !}
a↦→∣S∣≡𝟙 {S = e ∙ S} l ▸s = {!   !}



-- -- Non-values always reduce in well-resourced states

-- -- ▸-¬Val-⇒ : γ ⨾ δ ⨾ η ▸ ⟨ H , t , E , S ⟩ → ¬ Val t
-- --         → ∃₃ λ m n (s : State m n) → ⟨ H , t , E , S ⟩ ⇒ s
-- -- ▸-¬Val-⇒ {t = var x} ▸s ¬ev =
-- --   case ▸x→y↦ ▸s of λ
-- --     (_ , _ , _ , d) →
-- --   _ , _ , _ , varₕ d
-- -- ▸-¬Val-⇒ {t = lam p t} ▸s ¬ev =
-- --   ⊥-elim (¬ev lamᵥ)
-- -- ▸-¬Val-⇒ {t = t ∘⟨ p ⟩ u} ▸s ¬ev =
-- --   _ , _ , _ , appₕ
-- -- ▸-¬Val-⇒ {t = fst p t} ▸s ¬ev =
-- --   _ , _ , _ , fstₕ
-- -- ▸-¬Val-⇒ {t = snd p t} ▸s ¬ev =
-- --   _ , _ , _ , sndₕ
-- -- ▸-¬Val-⇒ {t = prodrec r p q A t u} ▸s ¬ev =
-- --   _ , _ , _ , prodrecₕ
-- -- ▸-¬Val-⇒ {t = prod s p t u} ▸s ¬ev =
-- --   ⊥-elim (¬ev prodᵥ)
-- -- ▸-¬Val-⇒ {t = unitrec p q A t u} ▸s ¬ev =
-- --   _ , _ , _ , unitrecₕ
-- -- ▸-¬Val-⇒ {t = star s} ▸s ¬ev =
-- --   ⊥-elim (¬ev starᵥ)
-- -- ▸-¬Val-⇒ {t = t} ▸s ¬ev =
-- --   {!!}

-- -- ▸-⇓→Ev : γ ⨾ δ ⨾ η ▸ ⟨ H , t , E , S ⟩
-- --        → ⟨ H , t , E , S ⟩ ⇓ ⟨ H′ , t′ , E′ , S′ ⟩
-- --        → Ev t′
-- -- ▸-⇓→Ev {t′} ▸s (d , ¬d′) =
-- --   case dec-Ev t′ of λ {
-- --     (yes evT) → evT ;
-- --     (no ¬evT) →
-- --       case ▸-⇒* ▸s d of λ
-- --     (_ , _ , _ , ▸s′) →
-- --       ⊥-elim (¬d′ (▸-¬Ev-⇒ ▸s′ ¬evT)) }

private
  variable
    e : Elim _ _ _

opaque

  -- The multiplicity of a well-resourced eliminator is not zero
  ▸∣e∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
         → γ ▸ᵉ e → ∣ e ∣ᵉ ≢ 𝟘
  ▸∣e∣≢𝟘 (-∘ₑ x) = non-trivial
  ▸∣e∣≢𝟘 ((x ∘ₑ-) p≢𝟘) = p≢𝟘
  ▸∣e∣≢𝟘 sucₑ = non-trivial
  ▸∣e∣≢𝟘 !-ₑ = ω≢𝟘
  ▸∣e∣≢𝟘 ⟨-, x ⟩ₑ = non-trivial
  ▸∣e∣≢𝟘 ⟨ x ,-⟩ₑ = non-trivial
  ▸∣e∣≢𝟘 (let⊗[-]ₑ x) = non-trivial
  ▸∣e∣≢𝟘 (let⋆[-]ₑ x) = non-trivial
  ▸∣e∣≢𝟘 (let![-]ₑ x) = non-trivial
  ▸∣e∣≢𝟘 (linearlyₑ x) = non-trivial
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
  ▸∣S∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
        → γ ▸ˢ S
        → ∣ S ∣ ≢ 𝟘
  ▸∣S∣≢𝟘 ε = non-trivial
  ▸∣S∣≢𝟘 (▸e ∙ ▸S) ∣eS∣≡𝟘 =
    let ∣S∣≢𝟘 = ▸∣S∣≢𝟘 ▸S
        ∣e∣≢𝟘 = ▸∣e∣≢𝟘 ▸e
     in case zero-product ∣eS∣≡𝟘 of λ where
          (inj₁ ∣S∣≡𝟘) → ∣S∣≢𝟘 ∣S∣≡𝟘
          (inj₂ ∣e∣≡𝟘) → ∣e∣≢𝟘 ∣e∣≡𝟘

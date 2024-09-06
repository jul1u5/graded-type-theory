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
import Tools.Reasoning.PartialOrder as RPo

open import Data.Fin using () renaming (fromℕ< to fromNat<; toℕ to toNat)
open import Data.Vec using (Vec; lookup; _[_]≔_; replicate)

private variable
  n m : Nat
  Γ Δ : Con _
  γ δ η : Conₘ _
  H H′ : Heap _
  x : _ ∋ᶜ _
  a : _ ∋ᶜ ref
  E E′ : Ren _ _
  A B : Type
  t t′ : _ ⊢ _
  v v′ : _ ⊢ᵥ _
  p p′ q q′ r r′ : M
  s s′ : State _ _ _ _
  S S′ : Stack _ _ _
  𝓐 𝓑 : ConItem _
  o : HeapObject _ _
  -- c : Closureₘ _ _
  -- c′ : Closure _ _

-- -- Subsumption for closures

-- subᶜ : γ ⨾ p ▸ᵒ o → p ≤ q → γ ⨾ q ▸ᵒ o
-- subᶜ (▸ᶜ ▸t p′≤p) p≤q = ▸ᶜ ▸t (≤-trans p′≤p p≤q)

-- -- Subsumption for heaps

-- subₕ : γ ▸ʰ H → γ ≤ᶜ δ → δ ▸ʰ H
-- subₕ {δ = ε} ε ε = ε
-- subₕ {δ = δ ∙ p} (▸H ∙ ▸c) (γ≤δ ∙ p″≤p) =
--   subₕ ▸H (+ᶜ-monotone γ≤δ (·ᶜ-monotoneˡ p″≤p)) ∙ subᶜ ▸c p″≤p

-- -- A well-resourced heap under the zero-context has all grades bounded by 𝟘.

-- 𝟘▸H→H≤𝟘 : 𝟘ᶜ ▸ʰ H → H ≤ʰ 𝟘
-- 𝟘▸H→H≤𝟘 ε = ε
-- 𝟘▸H→H≤𝟘 (_∙_ {E = E} {δ} ▸H (▸ᶜ _ p≤𝟘)) =
--   𝟘▸H→H≤𝟘 (subst (_▸ʰ _) (≈ᶜ→≡ lemma) ▸H) ∙ p≤𝟘
--   where
--   open import Tools.Reasoning.Equivalence Conₘ-setoid
--   lemma = begin
--     𝟘ᶜ +ᶜ 𝟘 ·ᶜ wkConₘ E δ  ≈⟨ +ᶜ-identityˡ _ ⟩
--     𝟘 ·ᶜ wkConₘ E δ        ≈⟨ ·ᶜ-zeroˡ _ ⟩
--     𝟘ᶜ                     ∎

-- private

--   -- A lemma relating modes and subtraction

--   mp-q≡r→m≡𝟙 : ∀ m → q ≢ 𝟘 → ⌜ m ⌝ · p - q ≡ r → m ≡ 𝟙ᵐ
--   mp-q≡r→m≡𝟙 𝟘ᵐ q≢𝟘 x =
--     ⊥-elim (𝟘-q≢p q≢𝟘 (subst (λ x → x - _ ≡ _) (·-zeroˡ _) x))
--   mp-q≡r→m≡𝟙 𝟙ᵐ _ _ = refl

-- -- In a well-resorced heap, a pointer lookup yields a well-resourced
-- -- term and a well-resourced heap.

-- ▸-heapLookup : H ⊢ y ↦[ q ] t , E ⨾ H′
--              → γ ▸ʰ H
--              → γ ⟨ y ⟩ - q ≤ r
--              → q ≢ 𝟘
--              → ∃ λ δ → δ ▸ t × (γ , y ≔ r) +ᶜ q ·ᶜ wkConₘ E δ ▸ʰ H′
-- ▸-heapLookup {q} {r} (here {r = r′} mp′-q≡r′)
--     (_∙_ {p} {m} ▸H (▸ᶜ {q = p′} ▸t mp′≤p)) p-q≤r q≢𝟘 =
--   case mp-q≡r→m≡𝟙 m q≢𝟘 mp′-q≡r′ of λ {
--     refl →
--   _ , ▸t
--     , subₕ ▸H lemma₁ ∙ ▸ᶜ¹ ▸t lemma₂ }
--   where
--   lemma₁ : ∀ {n} {γ δ : Conₘ n} → γ +ᶜ p ·ᶜ δ ≤ᶜ (γ +ᶜ q ·ᶜ δ) +ᶜ (r + q · 𝟘) ·ᶜ δ
--   lemma₁ {γ} {δ} = begin
--     γ +ᶜ p ·ᶜ δ                       ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneˡ p-q≤r) ⟩
--     γ +ᶜ (r + q) ·ᶜ δ                 ≈⟨ +ᶜ-congˡ (·ᶜ-distribʳ-+ᶜ r q δ) ⟩
--     γ +ᶜ (r ·ᶜ δ +ᶜ q ·ᶜ δ)           ≈⟨ +ᶜ-congˡ (+ᶜ-comm (r ·ᶜ δ) (q ·ᶜ δ)) ⟩
--     γ +ᶜ (q ·ᶜ δ +ᶜ r ·ᶜ δ)           ≈˘⟨ +ᶜ-assoc γ (q ·ᶜ δ) (r ·ᶜ δ) ⟩
--     (γ +ᶜ q ·ᶜ δ) +ᶜ r ·ᶜ δ           ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-identityʳ r)) ⟩
--     (γ +ᶜ q ·ᶜ δ) +ᶜ (r + 𝟘) ·ᶜ δ     ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-congˡ (·-zeroʳ q))) ⟩
--     (γ +ᶜ q ·ᶜ δ) +ᶜ (r + q · 𝟘) ·ᶜ δ ∎
--     where
--     open RPo ≤ᶜ-poset
--   lemma₂ : r′ ≤ r + q · 𝟘
--   lemma₂ = begin
--     r′ ≤⟨ -≡≤-monotoneˡ mp′≤p mp′-q≡r′ p-q≤r ⟩
--     r ≈˘⟨ +-identityʳ r ⟩
--     r + 𝟘 ≈˘⟨ +-congˡ (·-zeroʳ q) ⟩
--     r + q · 𝟘 ∎
--     where
--     open RPo ≤-poset
-- ▸-heapLookup {H = H ∙ (p′ , u , E)} {y +1} {q} {γ = γ ∙ p} {r}
--     (there {c = _ , E′} d) (_∙_ {δ} ▸H (▸ᶜ ▸u p′≤p)) γ⟨y⟩-q≤r q≢𝟘 =
--   case p+q-r≤p-r+q γ⟨y⟩-q≤r ((p ·ᶜ wkConₘ E δ) ⟨ y ⟩) of λ
--     γ⟨y⟩+pδ⟨y⟩-q≤pδ⟨y⟩+r →
--   case subst (_- q ≤ ((p ·ᶜ wkConₘ E δ) ⟨ y ⟩ + r))
--          (sym (lookup-distrib-+ᶜ γ (p ·ᶜ wkConₘ E δ) y))
--          γ⟨y⟩+pδ⟨y⟩-q≤pδ⟨y⟩+r of λ
--     γ+pδ⟨y⟩-q≤pδ⟨y⟩+r →
--   case ▸-heapLookup d ▸H γ+pδ⟨y⟩-q≤pδ⟨y⟩+r q≢𝟘 of λ
--     (δ′ , ▸t , ▸H′) →
--   _ , ▸t
--     , subₕ ▸H′ lemma₁
--     ∙ ▸ᶜ ▸u lemma₂
--   where
--   lemma₁ : ∀ {δ δ′}
--          →  (γ +ᶜ p ·ᶜ δ , y ≔ (p ·ᶜ δ) ⟨ y ⟩ + r) +ᶜ q ·ᶜ δ′
--          ≤ᶜ ((γ , y ≔ r) +ᶜ q ·ᶜ δ′) +ᶜ (p + q · 𝟘) ·ᶜ δ
--   lemma₁ {δ} {δ′} = begin
--     (γ +ᶜ p ·ᶜ δ , y ≔ (p ·ᶜ δ) ⟨ y ⟩ + r) +ᶜ q ·ᶜ δ′         ≈⟨ +ᶜ-congʳ (update-congʳ (+-comm _ r)) ⟩
--     (γ +ᶜ p ·ᶜ δ , y ≔ r + (p ·ᶜ δ) ⟨ y ⟩) +ᶜ q ·ᶜ δ′         ≡⟨ cong (_+ᶜ _) (update-distrib-+ᶜ γ (p ·ᶜ δ) r _ y) ⟩
--     ((γ , y ≔ r) +ᶜ (p ·ᶜ δ , y ≔ (p ·ᶜ δ) ⟨ y ⟩)) +ᶜ q ·ᶜ δ′ ≡⟨ cong (λ x → (_ +ᶜ x) +ᶜ _) (update-self (p ·ᶜ δ) y) ⟩
--     ((γ , y ≔ r) +ᶜ p ·ᶜ δ) +ᶜ q ·ᶜ δ′                       ≈⟨ +ᶜ-assoc (γ , y ≔ r) (p ·ᶜ δ) (q ·ᶜ δ′) ⟩
--     (γ , y ≔ r) +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ δ′                         ≈⟨ +ᶜ-congˡ (+ᶜ-comm (p ·ᶜ δ) (q ·ᶜ δ′)) ⟩
--     (γ , y ≔ r) +ᶜ q ·ᶜ δ′ +ᶜ p ·ᶜ δ                         ≈˘⟨ +ᶜ-assoc (γ , y ≔ r) (q ·ᶜ δ′) (p ·ᶜ δ) ⟩
--     ((γ , y ≔ r) +ᶜ q ·ᶜ δ′) +ᶜ p ·ᶜ δ                       ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-identityʳ p)) ⟩
--     ((γ , y ≔ r) +ᶜ q ·ᶜ δ′) +ᶜ (p + 𝟘) ·ᶜ δ                 ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-congˡ (·-zeroʳ q))) ⟩
--     ((γ , y ≔ r) +ᶜ q ·ᶜ δ′) +ᶜ (p + q · 𝟘) ·ᶜ δ ∎
--     where
--     open RPo ≤ᶜ-poset
--   lemma₂ : p′ ≤ p + q · 𝟘
--   lemma₂ = begin
--     p′         ≤⟨ p′≤p ⟩
--     p          ≈˘⟨ +-identityʳ p ⟩
--     p + 𝟘      ≈˘⟨ +-congˡ (·-zeroʳ q) ⟩
--     p + q · 𝟘  ∎
--     where
--     open RPo ≤-poset

-- -- The multiplicity of a well-resourced stack is not zero

-- ▸∣S∣≢𝟘 : η ▸ˢ S → ∣ S ∣ ≢ 𝟘
-- ▸∣S∣≢𝟘 ε ∣S∣≡𝟘 = non-trivial ∣S∣≡𝟘
-- ▸∣S∣≢𝟘 (∘ₑ _ ∙ ▸S) ∣S∣≡𝟘 = ▸∣S∣≢𝟘 ▸S ∣S∣≡𝟘
-- ▸∣S∣≢𝟘 (fstₑ _ ∙ ▸S) ∣S∣≡𝟘 = ▸∣S∣≢𝟘 ▸S ∣S∣≡𝟘
-- ▸∣S∣≢𝟘 (sndₑ ∙ ▸S) ∣S∣≡𝟘 = ▸∣S∣≢𝟘 ▸S ∣S∣≡𝟘
-- ▸∣S∣≢𝟘 (prodrecₑ _ r≢𝟘 ∙ ▸S) ∣S∣r≡𝟘 =
--   case zero-product ∣S∣r≡𝟘 of λ where
--     (inj₁ ∣S∣≡𝟘) → ▸∣S∣≢𝟘 ▸S ∣S∣≡𝟘
--     (inj₂ r≡𝟘) → r≢𝟘 r≡𝟘
-- ▸∣S∣≢𝟘 (unitrecₑ _ ∙ ▸S) ∣S∣≡𝟘 = ▸∣S∣≢𝟘 ▸S ∣S∣≡𝟘

-- module _ (Unitrec-ok : ∀ {p q} → Unitrec-allowed p q → p ≤ 𝟙)
--          (Prodrec-ok : ∀ {p q r} → Prodrec-allowed r p q → r ≢ 𝟘)
--          where

--   -- Well-resourced states evaluate to well-resourced states

--   -- ▸-⇒ : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒ s′)
--   --     → ∃₃ (_⨾_⨾_▸ s′)
--   -- ▸-⇒ {γ} {δ} {η} {s = ⟨ H , var x , E , S ⟩} {s′ = ⟨ _ , _ , E′ , _ ⟩}
--   --     (▸H , ▸x , ▸S , γ≤) (varₕ _ d) =
--   --   case ▸-heapLookup d ▸H lemma₂ (▸∣S∣≢𝟘 ▸S) of λ
--   --     (δ′ , ▸t , ▸H′) →
--   --   _ , _ , _
--   --     , ▸H′ , ▸t , ▸S
--   --     , let open RPo ≤ᶜ-poset
--   --           Eδ′ = wkConₘ E′ δ′
--   --       in  begin
--   --         (γ , x′ ≔ η ⟨ x′ ⟩) +ᶜ ∣S∣ ·ᶜ Eδ′
--   --           ≤⟨ +ᶜ-monotoneˡ (update-monotoneˡ x′ lemma₁) ⟩
--   --         ((𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η , x′ ≔ η ⟨ x′ ⟩) +ᶜ ∣S∣ ·ᶜ Eδ′
--   --           ≈˘⟨ +ᶜ-congʳ (update-congʳ (+-identityˡ _)) ⟩
--   --         ((𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η , x′ ≔ 𝟘 + η ⟨ x′ ⟩) +ᶜ ∣S∣ ·ᶜ Eδ′
--   --           ≡⟨ cong (_+ᶜ (∣S∣ ·ᶜ Eδ′)) (update-distrib-+ᶜ _ η 𝟘 _ x′) ⟩
--   --         (((𝟘ᶜ , x′ ≔ ∣S∣) , x′ ≔ 𝟘) +ᶜ (η , x′ ≔ η ⟨ x′ ⟩)) +ᶜ ∣S∣ ·ᶜ Eδ′
--   --           ≡⟨ cong₂ (λ x y → (x +ᶜ y) +ᶜ (∣S∣ ·ᶜ Eδ′)) update-twice (update-self η x′) ⟩
--   --         ((𝟘ᶜ , x′ ≔ 𝟘) +ᶜ η) +ᶜ ∣S∣ ·ᶜ Eδ′
--   --           ≡⟨ cong (λ x → (x +ᶜ η) +ᶜ (∣S∣ ·ᶜ Eδ′)) 𝟘ᶜ,≔𝟘 ⟩
--   --         (𝟘ᶜ +ᶜ η) +ᶜ ∣S∣ ·ᶜ Eδ′
--   --           ≈⟨ +ᶜ-congʳ (+ᶜ-identityˡ η) ⟩
--   --         η +ᶜ ∣S∣ ·ᶜ Eδ′
--   --           ≈⟨ +ᶜ-comm η _ ⟩
--   --         ∣S∣ ·ᶜ Eδ′ +ᶜ η ∎
--   --   where
--   --   x′ = wkVar E x
--   --   Eδ = wkConₘ E δ
--   --   δ≤ = inv-usage-var ▸x
--   --   ∣S∣ = ∣ S ∣
--   --   lemma₁ : γ ≤ᶜ (𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η
--   --   lemma₁ = begin
--   --     γ                               ≤⟨ γ≤ ⟩
--   --     ∣S∣ ·ᶜ Eδ +ᶜ η                    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
--   --     ∣S∣ ·ᶜ wkConₘ E (𝟘ᶜ , x ≔ 𝟙) +ᶜ η ≡⟨ cong (λ x → ∣S∣ ·ᶜ x +ᶜ η) (wkUsageVar E x) ⟩
--   --     ∣S∣ ·ᶜ (𝟘ᶜ , x′ ≔ 𝟙) +ᶜ η         ≡˘⟨ cong (_+ᶜ η) (update-distrib-·ᶜ 𝟘ᶜ ∣S∣ 𝟙 x′) ⟩
--   --     (∣S∣ ·ᶜ 𝟘ᶜ , x′ ≔ ∣S∣ · 𝟙) +ᶜ η     ≈⟨ +ᶜ-congʳ (update-cong (·ᶜ-zeroʳ ∣S∣) (·-identityʳ ∣S∣)) ⟩
--   --     (𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η              ∎
--   --     where
--   --     open RPo ≤ᶜ-poset
--   --   lemma₂ : γ ⟨ x′ ⟩ - ∣S∣ ≤ η ⟨ x′ ⟩
--   --   lemma₂ = begin
--   --     γ ⟨ x′ ⟩                        ≤⟨ lookup-monotone x′ lemma₁ ⟩
--   --     ((𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η) ⟨ x′ ⟩     ≡⟨ lookup-distrib-+ᶜ (𝟘ᶜ , x′ ≔ ∣S∣) η x′ ⟩
--   --     (𝟘ᶜ , x′ ≔ ∣S∣) ⟨ x′ ⟩ + η ⟨ x′ ⟩  ≡⟨ cong (_+ η ⟨ x′ ⟩) (update-lookup 𝟘ᶜ x′) ⟩
--   --     ∣S∣ + η ⟨ x′ ⟩                    ≈⟨ +-comm ∣S∣ _ ⟩
--   --     η ⟨ x′ ⟩ + ∣S∣                    ∎
--   --     where
--   --     open RPo ≤-poset
--   -- ▸-⇒ (▸H , ▸x , ▸S , γ≤) (varₕ′ ¬tr d) =
--   --   ⊥-elim (¬tr tt)
--   -- ▸-⇒ {γ} {δ} {η} {s = ⟨ H , t ∘⟨ p ⟩ u , E , S ⟩}
--   --     (▸H , ▸t , ▸S , γ≤) appₕ =
--   --   case inv-usage-app ▸t of λ
--   --     (invUsageApp {δ = δ′} {(η′)} ▸t ▸u δ≤) →
--   --   _ , _ , _
--   --     , ▸H , ▸t
--   --     , ∘ₑ (▸-cong (trans (cong (_·ᵐ _) (sym (≢𝟘→⌞⌟≡𝟙ᵐ (▸∣S∣≢𝟘 ▸S)))) ⌞⌟·ᵐ) ▸u) ∙ ▸S
--   --     , (begin
--   --       γ                                                         ≤⟨ γ≤ ⟩
--   --       ∣ S ∣ ·ᶜ wkConₘ E δ +ᶜ η                                  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
--   --       ∣ S ∣ ·ᶜ wkConₘ E (δ′ +ᶜ p ·ᶜ η′) +ᶜ η                    ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ E)) ⟩
--   --       ∣ S ∣ ·ᶜ (wkConₘ E δ′ +ᶜ wkConₘ E (p ·ᶜ η′)) +ᶜ η         ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (wk-·ᶜ E))) ⟩
--   --       ∣ S ∣ ·ᶜ (wkConₘ E δ′ +ᶜ p ·ᶜ wkConₘ E η′) +ᶜ η           ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
--   --       (∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ E η′) +ᶜ η  ≈⟨ +ᶜ-assoc _ _ _ ⟩
--   --       ∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ E η′ +ᶜ η    ≈˘⟨ +ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-assoc _ p _)) ⟩
--   --       ∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ (∣ S ∣ · p) ·ᶜ wkConₘ E η′ +ᶜ η   ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
--   --       ∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ η +ᶜ (∣ S ∣ · p) ·ᶜ wkConₘ E η′   ∎)
--   --   where
--   --   open RPo ≤ᶜ-poset
--   -- ▸-⇒ {γ} {δ} {s = ⟨ H , _ , E , _ ∙ S ⟩}
--   --     (▸H , ▸t , _∙_ {γ = η} ▸e ▸S , γ≤) (lamₕ {p = p}) =
--   --   case ▸e of λ {
--   --     (∘ₑ {γ = γ′} ▸u) →
--   --   case inv-usage-lam ▸t of λ
--   --     (invUsageLam {δ = δ′} ▸t δ≤) →
--   --   _ , _ , _
--   --     , subₕ ▸H (≤ᶜ-trans γ≤ (≤ᶜ-reflexive (≈ᶜ-sym (+ᶜ-assoc _ _ _))))
--   --     ∙ ▸ᶜᵖ ▸u
--   --     , ▸t , wk-▸ˢ (step id) ▸S
--   --     , (begin
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ +ᶜ η ∙ ∣ S ∣ · p                    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ∙ ≤-refl ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ η ∙ ∣ S ∣ · p                   ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ (step id) S)) ∙ ·-congʳ (wk-∣S∣ (step id) S) ⟩
--   --         ∣ wk1ˢ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · p          ≈˘⟨ ≈ᶜ-refl ∙ ·-congˡ (·-identityˡ p) ⟩
--   --         ∣ wk1ˢ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · 𝟙 · p      ≈˘⟨ ≈ᶜ-refl ∙ +-identityʳ _ ⟩
--   --         ∣ wk1ˢ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · 𝟙 · p + 𝟘  ∎) }
--   --   where
--   --   open RPo ≤ᶜ-poset
--   -- ▸-⇒ {γ} {δ} {η} {s = ⟨ H , t , E , S ⟩}
--   --     (▸H , ▸t , ▸S , γ≤) fstₕ =
--   --   case inv-usage-fst ▸t of λ
--   --     (invUsageFst {δ = δ′} m eq ▸t δ≤ mp-cond) →
--   --   _ , _ , _
--   --     , ▸H , ▸t , fstₑ (mp-cond refl) ∙ ▸S
--   --     , (begin
--   --         γ                               ≤⟨ γ≤ ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ +ᶜ η        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ η       ≈˘⟨ +ᶜ-congˡ (+ᶜ-identityʳ η) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ η +ᶜ 𝟘ᶜ ∎)
--   --   where
--   --   open RPo ≤ᶜ-poset
--   -- ▸-⇒ {γ} {δ} {η} {s = ⟨ H , t , E , S ⟩}
--   --     (▸H , ▸t , ▸S , γ≤) sndₕ =
--   --   case inv-usage-snd ▸t of λ
--   --     (invUsageSnd {δ = δ′} ▸t δ≤) →
--   --  _ , _ , _ , ▸H , ▸t , sndₑ ∙ ▸S
--   --    , (begin
--   --        γ                               ≤⟨ γ≤ ⟩
--   --        ∣ S ∣ ·ᶜ wkConₘ E δ +ᶜ η        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
--   --        ∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ η       ≈˘⟨ +ᶜ-congˡ (+ᶜ-identityʳ η) ⟩
--   --        ∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ η +ᶜ 𝟘ᶜ ∎)
--   --  where
--   --  open RPo ≤ᶜ-poset
--   -- ▸-⇒ {γ} {δ} {s = ⟨ H , t , E , e ∙ S ⟩}
--   --     (▸H , ▸t , _∙_ {γ = η} ▸e ▸S , γ≤) (prodˢₕ₁ {p}) =
--   --   case inv-usage-prodˢ ▸t of λ
--   --     (invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤) →
--   --   case ▸e of λ {
--   --     (fstₑ p≤𝟙) →
--   --   _ , _ , _
--   --     , ▸H , ▸-cong (≢𝟘→ᵐ·≡ (λ { refl → 𝟘≰𝟙 p≤𝟙})) ▸t , ▸S
--   --     , (begin
--   --         γ ≤⟨ γ≤ ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ +ᶜ η +ᶜ 𝟘ᶜ         ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ η) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ +ᶜ η               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E (∧ᶜ-decreasingˡ (p ·ᶜ δ₁) δ₂))) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E (p ·ᶜ δ₁) +ᶜ η       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ(wk-≤ᶜ E (·ᶜ-monotoneˡ p≤𝟙))) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E (𝟙 ·ᶜ δ₁) +ᶜ η       ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ E (·ᶜ-identityˡ δ₁))) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ₁ +ᶜ η              ∎) }
--   --   where
--   --   open RPo ≤ᶜ-poset
--   -- ▸-⇒ {γ} {δ} {s = ⟨ H , t , E , e ∙ S ⟩}
--   --     (▸H , ▸t , _∙_ {γ = η} ▸e ▸S , γ≤) (prodˢₕ₂ {p}) =
--   --   case inv-usage-prodˢ ▸t of λ
--   --     (invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤) →
--   --   case ▸e of λ {
--   --     sndₑ →
--   --   _ , _ , _ , ▸H , ▸u , ▸S
--   --     , (begin
--   --         γ ≤⟨ γ≤ ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ +ᶜ η +ᶜ 𝟘ᶜ        ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ η) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ +ᶜ η              ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E (∧ᶜ-decreasingʳ (p ·ᶜ δ₁) δ₂))) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ₂ +ᶜ η              ∎) }
--   --   where
--   --   open RPo ≤ᶜ-poset
--   -- ▸-⇒ {γ} {δ} {η} {s = ⟨ H , _ , E , S ⟩}
--   --     (▸H , ▸t , ▸S , γ≤) (prodrecₕ {r} {p} {u}) =
--   --   case inv-usage-prodrec ▸t of λ
--   --     (invUsageProdrec {δ = δ′} {η = η′} ▸t ▸u _ ok δ≤) →
--   --   case subst₂ (λ x y → _ ∙ x ∙ y ▸ u)
--   --          (·-identityˡ (r · p))
--   --          (·-identityˡ r) ▸u of λ
--   --     ▸u′ →
--   --   case Prodrec-ok ok of
--   --     λ r≢𝟘 →
--   --   _ , _ , _
--   --     , ▸H , ▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸t
--   --     , prodrecₑ ▸u′ r≢𝟘 ∙ ▸S
--   --     , (begin
--   --        γ                                                          ≤⟨ γ≤ ⟩
--   --        ∣ S ∣ ·ᶜ wkConₘ E δ +ᶜ η                                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
--   --        ∣ S ∣ ·ᶜ wkConₘ E (r ·ᶜ δ′ +ᶜ η′) +ᶜ η                     ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ E)) ⟩
--   --        ∣ S ∣ ·ᶜ (wkConₘ E (r ·ᶜ δ′) +ᶜ wkConₘ E η′) +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ ∣ S ∣ _ _) ⟩
--   --        (∣ S ∣ ·ᶜ wkConₘ E (r ·ᶜ δ′) +ᶜ ∣ S ∣ ·ᶜ wkConₘ E η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
--   --        ∣ S ∣ ·ᶜ wkConₘ E (r ·ᶜ δ′) +ᶜ ∣ S ∣ ·ᶜ wkConₘ E η′ +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ E)) (+ᶜ-comm _ η) ⟩
--   --        ∣ S ∣ ·ᶜ r ·ᶜ wkConₘ E δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E η′     ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc ∣ S ∣ r _) ⟩
--   --        (∣ S ∣ · r) ·ᶜ wkConₘ E δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E η′    ∎)
--   --   where
--   --   open RPo ≤ᶜ-poset
--   -- ▸-⇒ {γ} {δ} {s = ⟨ H , _ , E , _ ∙ S ⟩}
--   --     (▸H , ▸t , _∙_ {γ = η} ▸e ▸S , γ≤) (prodʷₕ {p} {t₁} {t₂} {r} {E′}) =
--   --   case ▸e of λ {
--   --     (prodrecₑ {γ = γ′} ▸u r≢𝟘) →
--   --   case inv-usage-prodʷ ▸t of λ
--   --     (invUsageProdʷ {δ = δ′} {η = η′} ▸t₁ ▸t₂ δ≤) →
--   --   case (begin
--   --         γ                                                                                                               ≤⟨ γ≤ ⟩
--   --         (∣ S ∣ · r) ·ᶜ wkConₘ E δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′                                                          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
--   --         (∣ S ∣ · r) ·ᶜ wkConₘ E (p ·ᶜ δ′ +ᶜ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′                                            ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ E)) ⟩
--   --         (∣ S ∣ · r) ·ᶜ (wkConₘ E (p ·ᶜ δ′) +ᶜ wkConₘ E η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′                                 ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-·ᶜ E))) ⟩
--   --         (∣ S ∣ · r) ·ᶜ (p ·ᶜ wkConₘ E δ′ +ᶜ wkConₘ E η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′                                   ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ (∣ S ∣ · r) _ _) ⟩
--   --         ((∣ S ∣ · r) ·ᶜ p ·ᶜ wkConₘ E δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ E η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′                    ≈˘⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-assoc (∣ S ∣ · r) p _)) ⟩
--   --         (((∣ S ∣ · r) · p) ·ᶜ wkConₘ E δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ E η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′                   ≈⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-congʳ (·-assoc ∣ S ∣ r p))) ⟩
--   --         ((∣ S ∣ · r · p) ·ᶜ wkConₘ E δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ E η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′                     ≈⟨ +ᶜ-comm _ _ ⟩
--   --         (η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′) +ᶜ (∣ S ∣ · r · p) ·ᶜ wkConₘ E δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ E η′                     ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
--   --         (η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ E η′ +ᶜ (∣ S ∣ · r · p) ·ᶜ wkConₘ E δ′                     ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
--   --         ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ E η′) +ᶜ (∣ S ∣ · r · p) ·ᶜ wkConₘ E δ′                   ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-identityʳ _)) ⟩
--   --         ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ E η′) +ᶜ (∣ S ∣ · r · p + 𝟘) ·ᶜ wkConₘ E δ′               ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-congˡ (·-zeroʳ _))) ⟩
--   --         ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ E η′) +ᶜ (∣ S ∣ · r · p + (∣ S ∣ · r) · 𝟘) ·ᶜ wkConₘ E δ′ ∎) of λ
--   --     γ≤′ →
--   --   case subst₂ (λ x y → δ′ ⨾ x ▸ᶜ[ ⌞ p ⌟ ] (y , t₁ , E))
--   --          (trans lemma (sym (trans (+-congˡ (·-zeroʳ _)) (+-identityʳ _))))
--   --          lemma
--   --          (▸ᶜ ▸t₁ ≤-refl) of λ
--   --     ▸ᶜt₁ →
--   --   _ , _ , _
--   --     , subₕ ▸H γ≤′ ∙ ▸ᶜt₁ ∙ ▸ᶜ¹ ▸t₂ ≤-refl
--   --     , ▸u , wk-▸ˢ (step (step id)) ▸S
--   --     , ≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-comm η _) (+ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ (step (step id)) S)))
--   --         ∙ trans (·-congʳ (wk-∣S∣ (step (step id)) S)) (sym (+-identityʳ _))
--   --         ∙ trans (·-congʳ (wk-∣S∣ (step (step id)) S)) (sym (+-identityʳ _ ))) }
--   --     where
--   --     open RPo ≤ᶜ-poset
--   --     lemma′ : ∀ m → ⌞ p ⌟ ≡ m → ⌜ m ⌝ · (∣ S ∣ · r · p) ≡ ∣ S ∣ · r · p
--   --     lemma′ 𝟘ᵐ p≡m rewrite ⌞⌟≡𝟘ᵐ→≡𝟘 p≡m =
--   --       trans (·-zeroˡ _) (trans (sym (·-zeroʳ _)) (·-assoc _ _ _))
--   --     lemma′ 𝟙ᵐ _ = ·-identityˡ _
--   --     lemma : ⌜ ⌞ p ⌟ ⌝ · (∣ S ∣ · r · p) ≡ ∣ S ∣ · r · p
--   --     lemma = lemma′ ⌞ p ⌟ refl
--   -- ▸-⇒ {γ} {δ} {η} {s = ⟨ _ , _ , _ , S ⟩} (▸H , ▸t , ▸S , γ≤) (unitrecₕ {p} {E}) =
--   --   case inv-usage-unitrec ▸t of λ
--   --     (invUsageUnitrec {δ = δ′} {η = η′} ▸t ▸u _ ok δ≤) →
--   --   case Unitrec-ok ok of λ
--   --     p≤𝟙 →
--   --   _ , _ , _ , ▸H
--   --     , ▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ λ {refl → 𝟘≰𝟙 p≤𝟙}) ▸t
--   --     , unitrecₑ ▸u ∙ ▸S
--   --     , (begin
--   --         γ                                                    ≤⟨ γ≤ ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ +ᶜ η                             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E (p ·ᶜ δ′ +ᶜ η′) +ᶜ η               ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ E)) ⟩
--   --         ∣ S ∣ ·ᶜ (wkConₘ E (p ·ᶜ δ′) +ᶜ wkConₘ E η′) +ᶜ η    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotoneˡ (wk-≤ᶜ E (·ᶜ-monotoneˡ p≤𝟙)))) ⟩
--   --         ∣ S ∣ ·ᶜ (wkConₘ E (𝟙 ·ᶜ δ′) +ᶜ wkConₘ E η′) +ᶜ η    ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-≈ᶜ E (·ᶜ-identityˡ δ′)))) ⟩
--   --         ∣ S ∣ ·ᶜ (wkConₘ E δ′ +ᶜ wkConₘ E η′) +ᶜ η           ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
--   --         (∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ ∣ S ∣ ·ᶜ wkConₘ E η′) +ᶜ η  ≈⟨ +ᶜ-assoc _ _ _ ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ ∣ S ∣ ·ᶜ wkConₘ E η′ +ᶜ η    ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E η′    ∎)
--   --   where
--   --   open RPo ≤ᶜ-poset
--   -- ▸-⇒ {γ} {δ} {s = ⟨ _ , _ , _ , S ⟩}
--   --   (▸H , ▸star , _∙_ {γ = η} ▸e ▸S , γ≤) (starʷₕ {E} {E′}) =
--   --   case ▸e of λ {
--   --     (unitrecₑ {γ = δ′} ▸t) →
--   --   case inv-usage-starʷ ▸star of λ
--   --     δ≤𝟘 →
--   --   _ , _ , _ , ▸H , ▸t , ▸S
--   --     , (begin
--   --         γ                                                 ≤⟨ γ≤ ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ δ′  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤𝟘)) ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ δ′ ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ E) ⟩
--   --         ∣ S ∣ ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ δ′          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
--   --         𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ δ′                   ≈⟨ +ᶜ-identityˡ _ ⟩
--   --         η +ᶜ ∣ S ∣ ·ᶜ wkConₘ E′ δ′                         ≈⟨ +ᶜ-comm _ _ ⟩
--   --         ∣ S ∣ ·ᶜ wkConₘ E′ δ′ +ᶜ η                         ∎) }
--   --   where
--   --   open RPo ≤ᶜ-poset

--   -- ▸-⇒* : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒* s′)
--   --      → ∃₃ (_⨾_⨾_▸ s′)
--   -- ▸-⇒* ▸s id =
--   --   _ , _ , _ , ▸s
--   -- ▸-⇒* ▸s (d ⇨ d′) =
--   --   case ▸-⇒ ▸s d of λ
--   --     (_ , _ , _ , ▸s′) →
--   --   ▸-⇒* ▸s′ d′

inv-usage-var : ∀ {x : Γ ∋ᶜ 𝓐} {γ : Conₘ n}
              → γ ▸ (` x) → γ ≤ᶜ (𝟘ᶜ , toFin x ≔ 𝟙)
inv-usage-var var = ≤ᶜ-refl
inv-usage-var (sub γ▸x γ≤γ′) with inv-usage-var γ▸x
... | γ′≤δ = ≤ᶜ-trans γ≤γ′ γ′≤δ

infix  60 _⟪_⟫

_⟪_⟫ : {Γ : Con n} (γ : Conₘ n) → (x : Γ ∋ᶜ 𝓐) → M
γ ⟪ x ⟫ = γ ⟨ toFin x ⟩

module _ (subtraction-ok : Supports-subtraction) where

  -- In a well-resorced heap, lookup of q copies succeeds for pointers whose
  -- associated grade is at most p + q for some p.

  opaque

    ▸H→y↦ : {Γ : Con n} {H : Heap Γ} {𝓐 : ConItem A} {x : Γ ∋ᶜ 𝓐}
          → γ ▸ʰ H
          → γ ⟪ x ⟫ ≤ p + q
          → ∃₂ λ (o : HeapObject Γ 𝓐) H′ → H ⊢ x ↦[- q ] o ⨾ H′
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
          → {H : Heap Γ} {x : Δ ∋ᶜ 𝓐} {S : Stack Γ A B}
          → γ ⨾ δ ⨾ η ▸ ⟪ H , ` x , E , S ⟫
          → ∃₂ λ (o : HeapObject Γ 𝓐) H′ → H ⊢ renVar E x ↦[- ∣ S ∣ ] o ⨾ H′
    ▸s→y↦ {n} {m} {γ} {δ} {η} {E} {x} {S} (▸H , ▸t , ▸S , γ≤) =
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
        ∣ S ∣ · δ ⟨ i ⟩               ≤⟨ ·-monotoneʳ (lookup-monotone i (inv-usage-var ▸t)) ⟩
        ∣ S ∣ · (𝟘ᶜ , i ≔ 𝟙) ⟨ i ⟩    ≡⟨ cong (∣ S ∣ ·_) (update-lookup 𝟘ᶜ i) ⟩
        ∣ S ∣ · 𝟙                     ≈⟨ ·-identityʳ _ ⟩
        ∣ S ∣                         ∎
      lemma : γ ⟨ i′ ⟩ ≤ η ⟨ i′ ⟩ + ∣ S ∣
      lemma = begin
        γ ⟨ i′ ⟩                                 ≤⟨ lookup-monotone i′ γ≤ ⟩
        (∣ S ∣ ·ᶜ renConₘ E δ +ᶜ η) ⟨ i′ ⟩       ≡⟨ lookup-distrib-+ᶜ (∣ S ∣ ·ᶜ renConₘ E δ) η i′ ⟩
        (∣ S ∣ ·ᶜ renConₘ E δ) ⟨ i′ ⟩ + η ⟨ i′ ⟩ ≤⟨ +-monotoneˡ lemma′ ⟩
        ∣ S ∣ + η ⟨ i′ ⟩                         ≈⟨ +-comm _ _ ⟩
        η ⟨ i′ ⟩ + ∣ S ∣                         ∎

  opaque
    ▸H→a↦ : {Γ : Con n} {H : Heap Γ} {a : Γ ∋ᶜ ref}
          → γ ▸ʰ H
          → γ ⟪ a ⟫ ≡ 𝟙
          → ∃₂ λ (o : HeapObject Γ ref) H′ → H ⊢ a ↦[ 𝟙 - 𝟙 ] o ⨾ H′
    ▸H→a↦ {a = vz} (_∙_ {p} ▸H _) refl =
      _ , _ , vz[] (subtraction-ok (≤-reflexive (sym (+-identityˡ 𝟙))) .proj₂)
    ▸H→a↦ {n = 1+ n} {γ = γ ∙ r} {a = vs a} (_∙_ {p} {δ} ▸H _) γ⟨i⟩≤p+q =
      case ▸H→a↦ {a = a} ▸H lemma of λ
        (_ , _ , d) →
      _ , _ , vs[] d
      where
        -- open RPo ≤-poset
        lemma : (γ +ᶜ r ·ᶜ δ) ⟪ a ⟫ ≡ 𝟙
        lemma = {!   !} -- begin
          -- (γ +ᶜ r ·ᶜ δ) ⟪ a ⟫      ≡⟨ lookup-distrib-+ᶜ γ _ (toFin a) ⟩
          -- γ ⟪ a ⟫ + (r ·ᶜ δ) ⟪ a ⟫ ≤⟨ {! +-monotoneˡ γ⟨i⟩≤p+q !} ⟩
          -- (p + q) + (r ·ᶜ δ) ⟪ a ⟫ ≈⟨ +-assoc p q _ ⟩
          -- p + q + (r ·ᶜ δ) ⟪ a ⟫   ≈⟨ +-congˡ (+-comm q _) ⟩
          -- p + (r ·ᶜ δ) ⟪ a ⟫ + q   ≈˘⟨ +-assoc p _ q ⟩
          -- (p + (r ·ᶜ δ) ⟪ a ⟫) + q ≈⟨ ? ⟩
          -- {!   !} ∎

  opaque
    ▸s→a↦ : {Γ : Con n} {Δ : Con m} {E : Ren Γ Δ}
          → {H : Heap Γ} {a : Δ ∋ᶜ ref} {S : Stack Γ Arr B}
          → γ ⨾ δ ⨾ η ▸ ⟪ H , ` a , E , S ⟫
          → ∃₂ λ (o : HeapObject Γ ref) H′ → H ⊢ renVar E a ↦[ 𝟙 - 𝟙 ] o ⨾ H′
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

  -- A variant of the above property with usage of states and adapated for linearly rule

  ▸linearly→y↦
    : {Γ : Con n} {Δ : Con m}
    → {H : Heap Γ} {E : Ren Γ Δ} {S : Stack Γ (! A) B}
    → {x : Γ ∋ᶜ var Lin} {k : Δ ⊢ᵥ ! A}
    → γ ⨾ δ ⨾ η ▸ ⟪ H , ⦅ k ⦆ᵛ , E , linearlyₑ x ∙ S ⟫
    → H ⊢ x ↦[ 𝟘 - 𝟘 ] lin ⨾ H
  ▸linearly→y↦ {n} {m} {γ} {δ} {η} {Γ} {Δ} {E} {S} {x} (▸H , ▸t , ▸S , γ≤) =
    {!!}
    where
    open RPo ≤-poset
    i : Fin n
    i = toFin x
    lemma′ : (∣ S ∣ ·ᶜ renConₘ E δ) ⟨ i ⟩ ≤ ∣ S ∣
    lemma′ = begin
      (∣ S ∣ ·ᶜ renConₘ E δ) ⟨ i ⟩  ≈⟨ lookup-distrib-·ᶜ (renConₘ E δ) ∣ S ∣ i ⟩
      ∣ S ∣ · renConₘ E δ ⟨ i ⟩     ≡⟨ cong (∣ S ∣ ·_) {! wk-⟨⟩ E!} ⟩
      ∣ S ∣ · δ ⟨ {!i!} ⟩           ≡⟨ {!!} ⟩
      -- ∣ S ∣ · δ ⟨ i ⟩              ≤⟨ ·-monotoneʳ (lookup-monotone i (inv-usage-var {!!})) ⟩
      -- ∣ S ∣ · (𝟘ᶜ , i ≔ 𝟙) ⟨ i ⟩   ≡⟨ cong (∣ S ∣ ·_) (update-lookup 𝟘ᶜ i) ⟩
      -- ∣ S ∣ · 𝟙                    ≈⟨ ·-identityʳ _ ⟩
      ∣ S ∣                        ∎
    lemma : γ ⟨ i ⟩ ≤ η ⟨ i ⟩ + ∣ S ∣
    lemma = begin
      γ ⟨ i ⟩                                 ≤⟨ lookup-monotone i γ≤ ⟩
      ((∣ S ∣ · 𝟙) ·ᶜ renConₘ E δ +ᶜ η) ⟨ i ⟩ ≡⟨ cong (λ m → (m ·ᶜ renConₘ E δ +ᶜ η) ⟨ i ⟩) (·-identityʳ _) ⟩
      (∣ S ∣ ·ᶜ renConₘ E δ +ᶜ η) ⟨ i ⟩       ≡⟨ lookup-distrib-+ᶜ (∣ S ∣ ·ᶜ renConₘ E δ) η i ⟩
      (∣ S ∣ ·ᶜ renConₘ E δ) ⟨ i ⟩ + η ⟨ i ⟩  ≤⟨ +-monotoneˡ lemma′ ⟩
      ∣ S ∣ + η ⟨ i ⟩                         ≈⟨ +-comm _ _ ⟩
      η ⟨ i ⟩ + ∣ S ∣                         ∎

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
           → H ⊢ renVar E a ↦ array xs
           → γ ⨾ δ ⨾ η ▸ ⟪ H , ` a , E , S ⟫
           → ∃ λ H′ → H ⊢ renVar E a ↦[ 𝟙 - 𝟙 ] array xs ⨾ H′
  ▸a↦→a↦[] {E} d ▸s =
    case ▸s→a↦ {E = E} ▸s of λ
      (_ , _ , d′) →
    case lookup-det′ d (↦[]→↦ (𝟙 , d′)) of λ {
      refl →
    _ , d′ }

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
    : {E : Ren Γ Δ} {x : Γ ∋ᶜ var Lin} {t : Δ ⊢ ! A}
    → H ⊢ x ↦ lin → γ ⨾ δ ⨾ η ▸ ⟪ H , t , E , linearlyₑ x ∙ S ⟫
    → H ⊢ x ↦[ 𝟘 - 𝟘 ] o ⨾ H
  ▸linearly→↦[] d ▸s = {!!}
    -- case ▸linearly→y↦ {! ▸s !} of λ
    --   d′ →
    -- case lookup-det′ d (↦[]→↦ {! d′ !}) of λ {
    --   refl →
    -- _ , d′ }

  -- ▸write↦→↦[]
  --   : {x : Γ ∋ᶜ ref} {i : Fin n} {v : Nat} {xs : Vec Nat n}
  --   → H ⊢ wkVar E x ↦ o → γ ⨾ δ ⨾ η ▸ ⟪ H  , ` x , E , write₃ₑ (num (toNat i)) (num v) E ∙ S ⟫
  --   → ∃ λ H′ → H ⊢ wkVar E x ↦[ ∣ S ∣ ] o ⨾ H′
  -- ▸write↦→↦[] d ▸s =
  --   case {! ▸s !} of λ
  --     (_ , _ , d′) →
  --   case lookup-det′ d (↦[]→↦ {! d′ !}) of λ {
  --     refl →
  --   _ , d′ }

a↦→∣S∣≡𝟙 : {xs : Vec Nat n}
         → H ⊢ a ↦ array xs
         → γ ⨾ δ ⨾ η ▸ ⟪ H , ` a , E , S ⟫
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

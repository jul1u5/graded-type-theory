module ArrayLang.Bisimilarity where

open import Agda.Primitive

open import Function using (case_of_; _∋_)
open import Data.Fin using () renaming (fromℕ< to fromNat<; toℕ to toNat)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; lookup; _[_]≔_; replicate)

open import Tools.Bool
open import Tools.Unit
open import Tools.Fin
open import Tools.Nat hiding (_≤_)
open import Tools.Product
open import Tools.Sum using (inj₁; inj₂)
open import Tools.Relation
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

open import Graded.Modality.Variant lzero

variant = nr-available-and-𝟘ᵐ-allowed-if true

open import Graded.Modality.Instances.Linearity variant
  using (Linearity; linearityModality; linearity-has-well-behaved-zero)
open import Graded.Modality.Instances.Zero-one-many false
  using (+≡𝟙; 𝟙-𝟙≡𝟘; -≡→≡+)
  renaming (supports-subtraction to ok)
open import Graded.Modality Linearity

𝕄 = linearityModality

open Modality 𝕄

open Has-well-behaved-zero linearity-has-well-behaved-zero
  using (non-trivial)
open import Graded.Modality.Properties.Subtraction semiring-with-meet

open import Graded.Context 𝕄

open import ArrayLang.Syntax 𝕄
open import ArrayLang.Heap 𝕄
open import ArrayLang.Heap.Properties 𝕄
open import ArrayLang.Reduction 𝕄

open import ArrayLang.Usage.Properties 𝕄 -≡→≡+ +≡𝟙

-- write : Arr → (i : ℕ) → (v : ℕ) → Arr

-- let xs′ = xs [ i ]≔ x

-- Ungraded: Copying
-- ε ∙[   ] array xs ⊢ writeᵤ vz i x ⨾ ε ∙[   ] array xs ∙[   ] array xs′
-- ^^^^^^^^^^^^^^^^^                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
--         H₀                                     H₁

-- Pure: Graded + Copying
-- ε ∙[ 𝟙 ] array xs ⊢ writeₚ vz i x ⨾ ε ∙[ 𝟘 ] array xs ∙[ 𝟙 ] array xs′
-- ^^^^^^^^^^^^^^^^^                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
--         H₂                                     H₃


-- Mutable: Graded + InPlace
-- ε ∙[ 𝟙 ] array xs ⊢ writeₘ vz i x ⨾ ε ∙[ 𝟙 ] array xs′
-- ^^^^^^^^^^^^^^^^^                     ^^^^^^^^^^^^^^^^^^
--         H₄                                      H₅

private variable
  n m : Nat
  s s′ : State _ _ _ _
  e : Elim _ _ _
  H H′ H″ : Heap _
  t t′ u u′ : _ ⊢ _
  E E′ : Ren _ _
  S S′ : Stack _ _ _
  γ δ η : Conₘ _
  Γ Γ′ Δ Δ′ : Con _
  A A′ B B′ : Type

module _ where
  open import ArrayLang.Heap.Equality.UpToGrades 𝕄

  -- Given:
  -- Hᵤ  ~ Hₚ
  -- ⇓
  -- Hᵤ′
  --
  -- Find Hₚ′ such that:
  --       Hₚ
  --       ⇓
  -- Hᵤ′ ~ Hₚ′
  ungraded↝pure
    : {Γ : Con n} {Γ′ : Con m}
    → {s @(⟪ Hᵤ  , t  , E  , S  ⟫) : State Γ  Δ  A  B}
    → {s′@(⟪ Hᵤ′ , t′ , E′ , S′ ⟫) : State Γ′ Δ′ A′ B}
    → ⟪ Hᵤ , t , E , S ⟫ ⇒ᵤ ⟪ Hᵤ′ , t′ , E′ , S′ ⟫
    → {Hₚ : Heap Γ}
    → Hᵤ ~ʰ Hₚ
    → γ ⨾ δ ⨾ η ▸ ⟪ Hₚ , t , E , S ⟫
    → ∃ λ Hₚ′ → ⟪ Hₚ , t , E , S ⟫ ⇒ₚ ⟪ Hₚ′ , t′ , E′ , S′ ⟫ × Hᵤ′ ~ʰ Hₚ′
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (varᵤ v l)       H~H ▸s =
    case ▸↦→↦[] ok {E = E} (~ʰ-lookup H~H l) ▸s of λ { (_ , _ , l′) →
    _ , var v l′ , ~ʰ-trans H~H (update-~ʰ l′)
    }
  ungraded↝pure app₁               H~H ▸s = _ , app₁             , H~H
  ungraded↝pure app₂ₑ              H~H ▸s = _ , app₂ₑ            , H~H ∙ _
  ungraded↝pure (app₂ p≢𝟘)         H~H ▸s = _ , app₂ p≢𝟘         , H~H
  ungraded↝pure (app₃ u)           H~H ▸s = _ , app₃ u           , H~H ∙ _
  ungraded↝pure (suc₁ ¬value)      H~H ▸s = _ , suc₁ ¬value      , H~H
  ungraded↝pure (suc₂ t)           H~H ▸s = _ , suc₂ t           , H~H
  ungraded↝pure (box₁ ¬value)      H~H ▸s = _ , box₁ ¬value      , H~H
  ungraded↝pure (box₂ v)           H~H ▸s = _ , box₂ v           , H~H
  ungraded↝pure (prod₁ ¬v₁⊎¬v₂)    H~H ▸s = _ , prod₁ ¬v₁⊎¬v₂    , H~H
  ungraded↝pure (prod₂ v₁)         H~H ▸s = _ , prod₂ v₁         , H~H
  ungraded↝pure (prod₃ v₁ v₂)      H~H ▸s = _ , prod₃ v₁ v₂      , H~H
  ungraded↝pure unit-elim₁         H~H ▸s = _ , unit-elim₁       , H~H
  ungraded↝pure unit-elim₂         H~H ▸s = _ , unit-elim₂       , H~H
  ungraded↝pure box-elim₁          H~H ▸s = _ , box-elim₁        , H~H
  ungraded↝pure (box-elim₂ v)      H~H ▸s = _ , box-elim₂ v      , H~H ∙ _
  ungraded↝pure prod-elim₁         H~H ▸s = _ , prod-elim₁       , H~H
  ungraded↝pure (prod-elim₂ v₁ v₂) H~H ▸s = _ , prod-elim₂ v₁ v₂ , H~H ∙ _ ∙ _
  ungraded↝pure linearly₁          H~H ▸s = _ , linearly₁        , H~H ∙ lin
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (linearly₂ v l)    H~H ▸s =
    _ , linearly₂ v (~ʰ-lookup H~H l)    , H~H
  ungraded↝pure consume₁           H~H ▸s = _ , consume₁         , H~H
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (consume₂ᵤ l)        H~H ▸s =
    let H-lin , l′ , ∣S∣≡𝟙 = ▸↦lin→↦[] ok {E = E} (~ʰ-lookup H~H l) ▸s
     in _ , consume₂ l′ (trans (sym (·-identityʳ _)) ∣S∣≡𝟙) , ~ʰ-trans H~H (update-~ʰ l′)
  ungraded↝pure duplicate₁         H~H ▸s = _ , duplicate₁       , H~H
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (duplicate₂ᵤ l)      H~H ▸s =
    let H-lin , l′ , ∣S∣≡𝟙 = ▸↦lin→↦[] ok {E = E} (~ʰ-lookup H~H l) ▸s
     in _ , duplicate₂ l′ (trans (sym (·-identityʳ _)) ∣S∣≡𝟙) , ~ʰ-trans H~H (update-~ʰ l′) ∙ _ ∙ _
  ungraded↝pure new₁               H~H ▸s = _ , new₁             , H~H
  ungraded↝pure (new₂ s t≡s)       H~H ▸s = _ , new₂ s t≡s       , H~H
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (new₃ᵤ s l)    H~H ▸s =
    let H-lin , l′ , ∣S∣≡𝟙 = ▸↦lin→↦[] ok {E = E} (~ʰ-lookup H~H l) ▸s
     in H-lin ∙[ 𝟙 ]ₕ array _ , new₃ s l′ (trans (sym (·-identityʳ _)) ∣S∣≡𝟙) , ~ʰ-trans H~H (update-~ʰ l′) ∙ _
  ungraded↝pure read₁              H~H ▸s = _ , read₁            , H~H
  ungraded↝pure (read₂ i t≡i)      H~H ▸s = _ , read₂ i t≡i      , H~H
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (read₃ᵤ i xs l)    H~H ▸s =
    let _ , l′ , ∣S∣≡𝟙 = ▸↦arr→↦[] ok {E = E} (~ʰ-lookup H~H l) ▸s
     in _ , read₃ i xs (↦[-]→↦[] l′) (trans (sym (·-identityʳ _)) ∣S∣≡𝟙) , H~H
  ungraded↝pure write₁             H~H ▸s = _ , write₁           , H~H
  ungraded↝pure (write₂ v t≡i)     H~H ▸s = _ , write₂ v t≡i     , H~H
  ungraded↝pure (write₃ i v t≡v)   H~H ▸s = _ , write₃ i v t≡v   , H~H
  ungraded↝pure {s = ⟪ H , _ , E , _ ⟫} (write₄ᵤ i v xs l) H~H ▸s =
    let o′ = array (xs [ i ]≔ v)
        H-arr , l′ , ∣S∣≡𝟙 = ▸↦arr→↦[] ok {E = E} (~ʰ-lookup H~H l) ▸s
     in H-arr ∙[ 𝟙 ]ₕ o′ , write₄ₚ i v xs l′ (trans (sym (·-identityʳ _)) ∣S∣≡𝟙) , ~ʰ-trans H~H (update-~ʰ l′) ∙ o′
  ungraded↝pure free₁        H~H ▸s = _ , free₁                  , H~H
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (free₂ᵤ l)    H~H ▸s =
    let H-arr , l′ , ∣S∣≡𝟙 = ▸↦arr→↦[] ok {E = E} (~ʰ-lookup H~H l) ▸s
     in H-arr , free₂ l′ (trans (sym (·-identityʳ _)) ∣S∣≡𝟙) , ~ʰ-trans H~H (update-~ʰ l′)

  pure↝ungraded
    : {Γ : Con n} {Γ′ : Con m}
    → {s @(⟪ Hₚ  , t  , E  , S  ⟫) : State Γ  Δ  A  B}
    → {s′@(⟪ Hₚ′ , t′ , E′ , S′ ⟫) : State Γ′ Δ′ A′ B}
    → ⟪ Hₚ , t , E , S ⟫ ⇒ₚ ⟪ Hₚ′ , t′ , E′ , S′ ⟫
    → {Hᵤ : Heap Γ}
    → Hₚ ~ʰ Hᵤ
    → ∃ λ Hᵤ′ → ⟪ Hᵤ , t , E , S ⟫ ⇒ᵤ ⟪ Hᵤ′ , t′ , E′ , S′ ⟫ × Hₚ′ ~ʰ Hᵤ′
  pure↝ungraded (var v l)            H~H = _ , varᵤ v (~ʰ-lookup H~H (↦[-]→↦ l))         , ~ʰ-trans (~ʰ-sym (update-~ʰ l)) H~H
  pure↝ungraded app₁                 H~H = _ , app₁                                      , H~H
  pure↝ungraded app₂ₑ                H~H = _ , app₂ₑ                                     , H~H ∙ _
  pure↝ungraded (app₂ p≢𝟘)           H~H = _ , app₂ p≢𝟘                                  , H~H
  pure↝ungraded (app₃ u)             H~H = _ , app₃ u                                    , H~H ∙ _
  pure↝ungraded (suc₁ ¬value)        H~H = _ , suc₁ ¬value                               , H~H
  pure↝ungraded (suc₂ t)             H~H = _ , suc₂ t                                    , H~H
  pure↝ungraded (box₁ ¬value)        H~H = _ , box₁ ¬value                               , H~H
  pure↝ungraded (box₂ v)             H~H = _ , box₂ v                                    , H~H
  pure↝ungraded (prod₁ ¬v₁⊎¬v₂)      H~H = _ , prod₁ ¬v₁⊎¬v₂                             , H~H
  pure↝ungraded (prod₂ v₁)           H~H = _ , prod₂ v₁                                  , H~H
  pure↝ungraded (prod₃ v₁ v₂)        H~H = _ , prod₃ v₁ v₂                               , H~H
  pure↝ungraded unit-elim₁           H~H = _ , unit-elim₁                                , H~H
  pure↝ungraded unit-elim₂           H~H = _ , unit-elim₂                                , H~H
  pure↝ungraded box-elim₁            H~H = _ , box-elim₁                                 , H~H
  pure↝ungraded (box-elim₂ v)        H~H = _ , box-elim₂ v                               , H~H ∙ _
  pure↝ungraded prod-elim₁           H~H = _ , prod-elim₁                                , H~H
  pure↝ungraded (prod-elim₂ v₁ v₂)   H~H = _ , prod-elim₂ v₁ v₂                          , H~H ∙ _ ∙ _
  pure↝ungraded linearly₁            H~H = _ , linearly₁                                 , H~H ∙ _
  pure↝ungraded (linearly₂ v l)      H~H = _ , linearly₂ v (~ʰ-lookup H~H l)             , H~H
  pure↝ungraded consume₁             H~H = _ , consume₁                                  , H~H
  pure↝ungraded (consume₂ l _)       H~H = _ , consume₂ᵤ (~ʰ-lookup H~H (↦[-]→↦ l))      , ~ʰ-trans (~ʰ-sym (update-~ʰ l)) H~H
  pure↝ungraded duplicate₁           H~H = _ , duplicate₁                                , H~H
  pure↝ungraded (duplicate₂ l _)     H~H = _ , duplicate₂ᵤ (~ʰ-lookup H~H (↦[-]→↦ l))    , ~ʰ-trans (~ʰ-sym (update-~ʰ l)) H~H ∙ _ ∙ _
  pure↝ungraded new₁                 H~H = _ , new₁                                      , H~H
  pure↝ungraded (new₂ s t≡s)         H~H = _ , new₂ s t≡s                                , H~H
  pure↝ungraded (new₃ s l _)         H~H = _ , new₃ᵤ s (~ʰ-lookup H~H (↦[-]→↦ l))        , ~ʰ-trans (~ʰ-sym (update-~ʰ l)) H~H ∙ _
  pure↝ungraded read₁                H~H = _ , read₁                                     , H~H
  pure↝ungraded (read₂ i t≡i)        H~H = _ , read₂ i t≡i                               , H~H
  pure↝ungraded (read₃ i xs l _)     H~H = _ , read₃ᵤ i xs (~ʰ-lookup H~H (↦[-]→↦ l))    , H~H
  pure↝ungraded write₁               H~H = _ , write₁                                    , H~H
  pure↝ungraded (write₂ v t≡i)       H~H = _ , write₂ v t≡i                              , H~H
  pure↝ungraded (write₃ i v t≡v)     H~H = _ , write₃ i v t≡v                            , H~H
  pure↝ungraded (write₄ₚ i v xs l _) H~H = _ , write₄ᵤ i v xs (~ʰ-lookup H~H (↦[-]→↦ l)) , ~ʰ-trans (~ʰ-sym (update-~ʰ l)) H~H ∙ _
  pure↝ungraded free₁                H~H = _ , free₁                                     , H~H
  pure↝ungraded (free₂ l _)          H~H = _ , free₂ᵤ (~ʰ-lookup H~H (↦[-]→↦ l))         , ~ʰ-trans (~ʰ-sym (update-~ʰ l)) H~H

module _ where
  open import ArrayLang.Heap.Equality.UpToRenaming 𝕄 𝟙-𝟙≡𝟘

  _~ˢ_ :
    ∀ {n n′ m m′}
    {Γₚ : Con n} {Γₘ : Con n′}
    {Δₚ : Con m} {Δₘ : Con m′} →
    State Γₚ Δₚ A B →
    State Γₘ Δₘ A B →
    Set
  _~ˢ_ {Γₚ = Γₚ} {Γₘ} ⟪ Hₚ , tₚ , Eₚ , Sₚ ⟫ ⟪ Hₘ , tₘ , Eₘ , Sₘ ⟫ =
    Σ (Ren Γₚ Γₘ)
    λ ρ
    → (Hₚ        ~ʰ[ ρ ] Hₘ)
    × (ren Eₚ tₚ ~ᵗ[ ρ ] ren Eₘ tₘ)
    × (Sₚ        ~S[ ρ ] Sₘ)

  --       ρ
  --    Ren Γₚ Γₘ
  -- Ren Eₚ    ⊩  Eₘ
  --    Ren Δₚ Δₘ
  --  tₚ   ?    tₘ

  -- ε ∙[ 𝟘 ] array xs ∙[ 𝟙 ] array xs′ ⊢ ` 1
  --
  --   liftRen (step id) : ε ∙ ref ∙ Ren ref ε ∙ ref
  --
  -- ε ∙[ 𝟙 ] array xs′ ⊢ ` 0

  record _∼ˢ-⇐_
    {n′ m′}
    {Γₚ′ : Con n′}
    {Δₚ′ : Con m′}
    (sₚ′ : State Γₚ′ Δₚ′ A′ B)
    {n m}
    {Γₘ : Con n} {Δₘ : Con m}
    (sₘ : State Γₘ Δₘ A B)
    : Set where
    constructor _red:_rel:_
    field
      {n″ m″} : Nat
      {Γₘ′} : Con n″
      {Δₘ′} : Con m″
      sₘ′   : State Γₘ′ Δₘ′ A′ B
      red   : sₘ ⇒ₘ sₘ′
      -- {ρ}   : Ren Γₚ′ Γₘ′
      rel   : sₚ′ ~ˢ sₘ′ -- [ ρ ]

  pure↝mutable :
    ∀ {n n′ m m′ : Nat}
    {Γₚ : Con n} {Γₚ′ : Con n′}
    {Δₚ : Con m} {Δₚ′ : Con m′}
    {sₚ  : State Γₚ  Δₚ  A  B}
    {sₚ′ : State Γₚ′ Δₚ′ A′ B} →
    sₚ ⇒ₚ sₚ′ →

    ∀ {k l}
    {Γₘ : Con k}
    {Δₘ : Con l}
    {sₘ  : State Γₘ Δₘ A B} →
    sₚ ~ˢ sₘ →

    ∀ {γ δ η} →
    γ ⨾ δ ⨾ η ▸ sₘ →
    sₚ′ ∼ˢ-⇐ sₘ
  pure↝mutable (var {E = Eₚ} {x = xₚ} v l) {sₘ = ⟪ H , ` xₘ , Eₘ , S ⟫} (ρ , H~H , var [Eₚ]xₚ [Eₚ]xₚ≡ρ[Eₘ]xₘ , S~S) (_ , _ , ▸S , _) =
    let ∣S∣≢𝟘 = subst (_≢ 𝟘) (sym (~S→∣≡∣ S~S)) (▸∣S∣≢𝟘 ok ▸S) in
    case ~ʰ-lookup′ H~H l ∣S∣≢𝟘 of λ { (H′ , yₘ , value v′ E′ , lₘ , [Eₚ]xₚ≡ρyₘ , refl , H′~H′) →
    let yₘ≡[Eₘ]xₘ = renVar-inj ρ _ _ (trans (sym [Eₚ]xₚ≡ρyₘ) [Eₚ]xₚ≡ρ[Eₘ]xₘ)
        lₘ′ = subst₂ (_ ⊢_↦[ _ -_] value v′ E′ ⨾ _) yₘ≡[Eₘ]xₘ (~S→∣≡∣ S~S) lₘ
     in ⟪ _ , ⦅ v′ ⦆ᵛ , E′ , S ⟫
        red: (var v′ lₘ′)
        rel: (ρ , H′~H′ , ≡→~ᵗ (sym (ren-comp ρ _ ⦅ v ⦆ᵛ)) , S~S)
    }
  pure↝mutable app₁ {sₘ = ⟪ _ , _ ∘ _ , _ , _ ⟫} (ρ , H~H , t~t ∘ u~u , S~S) _ =
    _
    red: app₁
    rel: (ρ , H~H , t~t , (-∘ₑ u~u) ∙ S~S)
  pure↝mutable app₂ₑ {sₘ = ⟪ H , lam _ t , E , (-∘ₑ u) E′ ∙ S ⟫} (ρ , H~H , lam _ t~t , ((-∘ₑ u~u) ∙ S~S)) _ =
    ⟪ H ∙[ 𝟘 ]ₕ ↯ , t , liftRen E , ren1ˢ _ S ⟫
    red: app₂ₑ
    rel: (liftRen ρ , ~ʰ′-extend H~H , t~t , ~S-ren1 S~S)
  pure↝mutable (app₂ p≢𝟘) {sₘ = ⟪ H , lam p t , E , (-∘ₑ u) E′ ∙ S ⟫} (ρ , H~H , lam p t~t , ((-∘ₑ u~u) ∙ S~S)) _ =
    ⟪ H , u , E′ , ((_ , lam p t) ∘ₑ-) E ∙ S ⟫
    red: app₂ p≢𝟘
    rel: (ρ , H~H , u~u , (lam p t~t ∘ₑ-) ∙ S~S)
  pure↝mutable (app₃ (uₚ , value-uₚ)) {sₘ = ⟪ H , u , E , ((_ , lam p t) ∘⟨ p ⟩ₑ-) E′ ∙ S ⟫} (ρ , H~H , u~u , ((lam p t~t ∘ₑ-) ∙ S~S)) _ =
    let value-uₘ = ~ᵗ-subst-value u~u value-uₚ in
    ⟪ H ∙[ ∣ S ∣ · p ]ₕ value (u , value-uₘ) E , t , liftRen E′ , ren1ˢ _ S ⟫
    red: app₃ (u , value-uₘ)
    rel: (liftRen ρ , ~ʰ-cons-value H~H u~u value-uₚ S~S , t~t , ~S-ren1 S~S)
  pure↝mutable (suc₁ ¬value-t) {sₘ = ⟪ H , suc t , E , S ⟫} (ρ , H~H , suc t~t , S~S) _ =
    ⟪ H , t , E , sucₑ ∙ S ⟫
    red: suc₁ (~ᵗ-subst-¬value t~t ¬value-t)
    rel: (ρ , H~H , t~t , sucₑ ∙ S~S)
  pure↝mutable (suc₂ value-tₚ) {sₘ = ⟪ H , t , E , sucₑ ∙ S ⟫} (ρ , H~H , t~t , sucₑ ∙ S~S) _ =
    let value-t = ~ᵗ-subst-value t~t value-tₚ in
    ⟪ H , suc t , E , S ⟫
    red: suc₂ value-t
    rel: (ρ , H~H , suc t~t , S~S)
  pure↝mutable (box₁ ¬value-t)     {sₘ = ⟪ H , ! t , E , S ⟫} (ρ , H~H , ! t~t , S~S) _ =
    _
    red: box₁ (~ᵗ-subst-¬value t~t ¬value-t)
    rel: (ρ , H~H , t~t , !-ₑ ∙ S~S)
  pure↝mutable (box₂ v)     {sₘ = ⟪ H , t , E , !-ₑ ∙ S ⟫} (ρ , H~H , t~t , !-ₑ ∙ S~S) _ =
    let v′ = ~ᵗ-subst-value t~t v in
    ⟪ H , ! t , E , S ⟫
    red: box₂ v′
    rel: (ρ , H~H , ! t~t , S~S)
  pure↝mutable (prod₁ ¬value-t₁⊎¬value-t₂)    {sₘ = ⟪ H , ⟨ t₁ , t₂ ⟩ , E , S ⟫} (ρ , H~H , ⟨ ~₁ , ~₂ ⟩ , S~S) _ =
    _
    red: prod₁ (case ¬value-t₁⊎¬value-t₂ of λ where
      (inj₁ ¬value-t₁) → inj₁ (~ᵗ-subst-¬value ~₁ ¬value-t₁)
      (inj₂ ¬value-t₂) → inj₂ (~ᵗ-subst-¬value ~₂ ¬value-t₂))
    rel: (ρ , H~H , ~₁ , ⟨-, ~₂ ⟩ₑ ∙ S~S)
  pure↝mutable (prod₂ v₁)    (ρ , H~H , ~₁ , ⟨-, ~₂ ⟩ₑ ∙ S~S) _ =
    _
    red: prod₂ (~ᵗ-subst-value ~₁ v₁)
    rel: (ρ , H~H , ~₂ , ⟨ ~₁ ,-⟩ₑ ∙ S~S)
  pure↝mutable (prod₃ {t₁} value-tₚ₁ value-tₚ₂)   {sₘ = ⟪ H , tₘ₂ , E₂ , ⟨ (tₘ₁ , value-tₘ₁) ,-⟩ₑ E₁ ∙ S ⟫} (ρ , H~H , ~₂ , ⟨ ~₁ ,-⟩ₑ ∙ S~S) _ =
    _
    red: prod₃ value-tₘ₁ (~ᵗ-subst-value ~₂ value-tₚ₂)
    rel: (ρ , H~H , ⟨ ≡→~ᵗ lemma , ≡→~ᵗ lemma′ ⟩ , S~S)
    where
      lemma : ren idRen (ren _ t₁) ≡ ren ρ (ren idRen (ren E₁ tₘ₁))
      lemma = begin
        ren idRen (ren _ t₁)           ≡⟨ ren-id _ ⟩
        ren _ t₁                       ≡⟨ ~ᵗ→≡ ~₁ ⟩
        ren ρ (ren E₁ tₘ₁)             ≡˘⟨ cong (λ ρ → ren ρ _) (•-identityʳ ρ) ⟩
        ren (ρ • idRen) (ren E₁ tₘ₁)   ≡˘⟨ ren-comp ρ idRen _ ⟩
        ren ρ (ren idRen (ren E₁ tₘ₁)) ∎

      lemma′ : ren idRen (ren _ _) ≡ ren ρ (ren idRen (ren E₂ tₘ₂))
      lemma′ = begin
        ren idRen (ren _ _)            ≡⟨ ren-id _ ⟩
        ren _ _                        ≡⟨ ~ᵗ→≡ ~₂ ⟩
        ren ρ (ren E₂ tₘ₂)             ≡˘⟨ cong (λ ρ → ren ρ _) (•-identityʳ ρ) ⟩
        ren (ρ • idRen) (ren E₂ tₘ₂)   ≡˘⟨ ren-comp ρ idRen _ ⟩
        ren ρ (ren idRen (ren E₂ tₘ₂)) ∎
  pure↝mutable unit-elim₁ {sₘ = ⟪ H , let⋆[ t ] u , E , S ⟫} (ρ , H~H , let⋆[ t~t ] u~u , S~S) _ =
    _
    red: unit-elim₁
    rel: (ρ , H~H , t~t , let⋆[-]ₑ u~u ∙ S~S)
  pure↝mutable unit-elim₂ {sₘ = ⟪ H , star , _ , let⋆[-]ₑ u E ∙ S ⟫} (ρ , H~H , star , let⋆[-]ₑ u~u ∙ S~S) _ =
    _
    red: unit-elim₂
    rel: (ρ , H~H , u~u , S~S)
  pure↝mutable box-elim₁ {sₘ = ⟪ H , let![ t ] u , E , S ⟫} (ρ , H~H , let![ t~t ] u~u , S~S) _ =
    _
    red: box-elim₁
    rel: (ρ , H~H , t~t , let![-]ₑ u~u ∙ S~S)
  pure↝mutable (box-elim₂ (_ , v)) {sₘ = ⟪ H , ! _ , E′ , let![-]ₑ u E ∙ S ⟫} (ρ , H~H , ! t~t , let![-]ₑ u~u ∙ S~S) _ =
    _
    red: box-elim₂ (_ , ~ᵗ-subst-value t~t v)
    rel: (liftRen ρ , ~ʰ-cons-value H~H t~t v S~S , u~u , ~S-ren1 S~S)
  pure↝mutable prod-elim₁ {sₘ = ⟪ H , let⊗[ t ] u , E , S ⟫} (ρ , H~H , let⊗[ t~t ] u~u , S~S) _ =
    _
    red: prod-elim₁
    rel: (ρ , H~H , t~t , let⊗[-]ₑ u~u ∙ S~S)
  pure↝mutable (prod-elim₂ v₁ v₂) {sₘ = ⟪ H , ⟨ t₁ , t₂ ⟩ , E′ , let⊗[-]ₑ u E ∙ S ⟫} (ρ , H~H , ⟨ ~₁ , ~₂ ⟩ , let⊗[-]ₑ u~u ∙ S~S) _ =
    _
    red: prod-elim₂ (~ᵗ-subst-value ~₁ v₁) (~ᵗ-subst-value ~₂ v₂)
    rel: (liftRen (liftRen ρ) , {! ~ʰ-cons-value′ (~ʰ-cons-value′ ? ? ? ?) ? ? ?  !} , u~u , ~S-ren1 (~S-ren1 S~S))
  pure↝mutable linearly₁ {sₘ = ⟪ H , linearly t , E , S ⟫} (ρ , H~H , linearly t~t , S~S) _ =
    ⟪ H ∙[ 𝟙 ]ₕ lin , t , liftRen E , linearlyₑ vz ∙ ren1ˢ _ S ⟫
    red: linearly₁
    rel: (liftRen ρ , ~ʰ′-extend H~H , t~t , linearlyₑ {x = vz} ∙ ~S-ren1 S~S)
  pure↝mutable (linearly₂ (k , value-k) (_ , d)) {sₘ = ⟪ H , t , E , linearlyₑ x ∙ S ⟫} (ρ , H~H , t~t , linearlyₑ ∙ S~S) _ =
    let _ , d′ , _ = ~ʰ-lookup H~H (inj₁ λ ()) d in
    _
    red: linearly₂ (_ , ~ᵗ-subst-value t~t value-k) (_ , ↦[-]→↦[] d′)
    rel: (ρ , H~H , t~t , S~S)
  pure↝mutable consume₁   {sₘ = ⟪ H , consume t , E , S ⟫} (ρ , H~H , consume t~t , S~S) ▸s =
    _
    red: consume₁
    rel: (ρ , H~H , t~t , (consumeₑ ∙ S~S))
  pure↝mutable (consume₂ l ∣S∣≡𝟙)   {sₘ = ⟪ H , ` t , E , consumeₑ ∙ S ⟫} (ρ , H~H , var [Eₚ]xₚ [Eₚ]xₚ≡ρ[Eₘ]xₘ , consumeₑ ∙ S~S) _ =
    let ∣S∣≡𝟙 = subst (_≡ 𝟙) (~S→∣≡∣ S~S) ∣S∣≡𝟙
        _ , l′ , H~H = ~ʰ-lookup H~H (inj₁ λ ()) (subst (_ ⊢_↦[ 𝟙 - 𝟙 ] _ ⨾ _) [Eₚ]xₚ≡ρ[Eₘ]xₘ l)
    in
    _
    red: consume₂ l′ ∣S∣≡𝟙
    rel: (ρ , H~H , star , S~S)
  pure↝mutable duplicate₁     {sₘ = ⟪ H , duplicate t , E , S ⟫} (ρ , H~H , duplicate t~t , S~S) ▸s =
    _
    red: duplicate₁
    rel: (ρ , H~H , t~t , (duplicateₑ ∙ S~S))
  pure↝mutable (duplicate₂ l ∣S∣≡𝟙) {sₘ = ⟪ H , ` t , E , duplicateₑ ∙ S ⟫} (ρ , H~H , var [Eₚ]xₚ [Eₚ]xₚ≡ρ[Eₘ]xₘ , duplicateₑ ∙ S~S) ▸s =
    let ∣S∣≡𝟙 = subst (_≡ 𝟙) (~S→∣≡∣ S~S) ∣S∣≡𝟙
        _ , l′ , H~H = ~ʰ-lookup H~H (inj₁ λ ()) (subst (_ ⊢_↦[ 𝟙 - 𝟙 ] _ ⨾ _) [Eₚ]xₚ≡ρ[Eₘ]xₘ l)
    in
    _
    red: duplicate₂ l′ ∣S∣≡𝟙
    rel: (liftRen (liftRen ρ) , ~ʰ′-extend (~ʰ′-extend H~H) , ⟨ var (vs vz) refl , var vz refl ⟩ , ~S-ren1 (~S-ren1 S~S))
  pure↝mutable new₁              {sₘ = ⟪ H , new l s , E , S ⟫} (ρ , H~H , new l~l s~s , S~S) _ =
    ⟪ H , s , E , new₁ₑ l E ∙ S ⟫
    red: new₁
    rel: ( ρ , H~H , s~s , new₁ₑ l~l ∙ S~S )
  pure↝mutable (new₂ s refl)              {sₘ = ⟪ H , t , E′ , new₁ₑ l E ∙ S ⟫} (ρ , H~H , t~t , new₁ₑ l~l ∙ S~S) _ =
    ⟪ H , l , E , new₂ₑ s ∙ S ⟫
    red: new₂ s lemma
    rel: (ρ , H~H , l~l , new₂ₑ ∙ S~S)
    where
      lemma : t ≡ Nat→⊢ s
      lemma = inv-renNat→⊢ (inv-renNat→⊢ (begin
        ren ρ (ren E′ t) ≡˘⟨ ~ᵗ→≡ t~t ⟩
        ren _ (Nat→⊢ s) ≡⟨ renNat→⊢ s ⟩
        Nat→⊢ s ∎))
  pure↝mutable (new₃ s l ∣S∣≡𝟙)        {sₘ = ⟪ H , ` x , E , new₂ₑ s ∙ S ⟫} (ρ , H~H , var [Eₚ]xₚ [Eₚ]xₚ≡ρ[Eₘ]xₘ , new₂ₑ ∙ S~S) _ =
    let ∣S∣≡𝟙 = subst (_≡ 𝟙) (~S→∣≡∣ S~S) ∣S∣≡𝟙
        _ , l′ , H~H = ~ʰ-lookup H~H (inj₁ λ ()) (subst (_ ⊢_↦[ 𝟙 - 𝟙 ] _ ⨾ _) [Eₚ]xₚ≡ρ[Eₘ]xₘ l)
    in
    _
    red: new₃ s l′ ∣S∣≡𝟙
    rel: (liftRen ρ , ~ʰ′-extend H~H , var vz refl , ~S-ren1 S~S)
  pure↝mutable read₁             {sₘ = ⟪ H , read arr i , E , S ⟫} (ρ , H~H , read arr~arr i~i , S~S) _ =
    ⟪ H , i , E , read₁ₑ arr E ∙ S ⟫
    red: read₁
    rel: (ρ , H~H , i~i , (read₁ₑ arr~arr ∙ S~S))
  pure↝mutable (read₂ i refl)         {sₘ = ⟪ H , t , E′ , read₁ₑ arr E ∙ S ⟫} (ρ , H~H , t~t , read₁ₑ arr~arr ∙ S~S) _ =
    ⟪ H , arr , E , read₂ₑ i ∙ S ⟫
    red: read₂ i lemma
    rel: (ρ , H~H , arr~arr , (read₂ₑ ∙ S~S))
    where
      lemma : t ≡ Nat→⊢ i
      lemma = inv-renNat→⊢ (inv-renNat→⊢ (begin
        ren ρ (ren E′ t) ≡˘⟨ ~ᵗ→≡ t~t ⟩
        ren _ (Nat→⊢ i) ≡⟨ renNat→⊢ i ⟩
        Nat→⊢ i ∎))
  pure↝mutable (read₃ iₚ xs l ∣S∣≡𝟙)    {sₘ = ⟪ H , ` x , E , read₂ₑ i ∙ S ⟫} (ρ , H~H , var [Eₚ]xₚ [Eₚ]xₚ≡ρ[Eₘ]xₘ , read₂ₑ ∙ S~S) _ =
    let ∣S∣≡𝟙 = subst (_≡ 𝟙) (~S→∣≡∣ S~S) ∣S∣≡𝟙 in
    case ~ʰ-lookup H~H (inj₂ non-trivial) (subst (_ ⊢_↦[ 𝟙 ] _) [Eₚ]xₚ≡ρ[Eₘ]xₘ l) of λ { (_ , l′ , _) →
    ⟪ H , ⟨ ` x , _ ⟩ , E , S ⟫
    red: read₃ iₚ xs (↦[-]→↦[] l′) ∣S∣≡𝟙
    rel: (ρ , H~H , ⟨ var (renVar E x) [Eₚ]xₚ≡ρ[Eₘ]xₘ , ! ≡→~ᵗ lemma ⟩ , S~S)
    }
    where
      lemma : ren _ (Nat→⊢ (lookup xs iₚ)) ≡ ren ρ (ren E (Nat→⊢ (lookup xs iₚ)))
      lemma = begin
                       ren _ (Nat→⊢ (lookup xs iₚ))  ≡⟨ renNat→⊢ _ ⟩
                              Nat→⊢ (lookup xs iₚ)   ≡˘⟨ renNat→⊢ _ ⟩
                 ren (ρ • E) (Nat→⊢ (lookup xs iₚ))  ≡˘⟨ ren-comp _ _ _ ⟩
                ren ρ (ren E (Nat→⊢ (lookup xs iₚ))) ∎
  pure↝mutable write₁            {sₘ = ⟪ H , write arr i v , E , S ⟫} (ρ , H~H , write arr~arr i~i v~v , S~S) _ =
    ⟪ H , v , E , write₁ₑ arr i E ∙ S ⟫
    red: write₁
    rel: (ρ , H~H , v~v , (write₁ₑ arr~arr i~i ∙ S~S))
  pure↝mutable (write₂ v refl)        {sₘ = ⟪ H , t , E′ , write₁ₑ arr i E ∙ S ⟫} (ρ , H~H , t~t , write₁ₑ arr~arr i~i ∙ S~S) _ =
    _ -- ⟪ H , i , E , write₂ₑ arr v E ∙ S ⟫
    red: write₂ v lemma
    rel: (ρ , H~H , i~i , write₂ₑ arr~arr ∙ S~S)
    where
      lemma : t ≡ Nat→⊢ v
      lemma = inv-renNat→⊢ (inv-renNat→⊢ (begin
        ren ρ (ren E′ t) ≡˘⟨ ~ᵗ→≡ t~t ⟩
        ren _ (Nat→⊢ v) ≡⟨ renNat→⊢ v ⟩
        Nat→⊢ v ∎))
  pure↝mutable (write₃ i v refl)      {sₘ = ⟪ H , t , E′ , write₂ₑ arr v E ∙ S ⟫} (ρ , H~H , t~t , write₂ₑ arr~arr ∙ S~S) _ =
    _ -- ⟪ H , arr , E , write₃ₑ i v ∙ S ⟫
    red: write₃ i v lemma
    rel: (ρ , H~H , arr~arr , write₃ₑ ∙ S~S)
    where
      lemma : t ≡ Nat→⊢ i
      lemma = inv-renNat→⊢ (inv-renNat→⊢ (begin
        ren ρ (ren E′ t) ≡˘⟨ ~ᵗ→≡ t~t ⟩
        ren _ (Nat→⊢ i) ≡⟨ renNat→⊢ i ⟩
        Nat→⊢ i ∎))
  pure↝mutable
    (write₄ₚ {E = Eₚ} {x = xₚ} iFin v xs d ∣S∣≡𝟙)
    {sₘ = ⟪ H , ` xₘ , Eₘ , write₃ₑ i v ∙ S ⟫}
    (ρ , H~H , var [Eₘ]xₘ [Eₚ]xₚ≡ρ[Eₘ]xₘ , write₃ₑ ∙ S~S)
    ▸s =
    case ~ʰ-lookup′ H~H d non-trivial of λ { (_ , yₘ , array xs , dₘ , [Eₚ]xₚ≡ρyₘ , refl , H′~H′) →
    let ∣S∣≡𝟙 = subst (_≡ 𝟙) (~S→∣≡∣ S~S) ∣S∣≡𝟙
        d′ = subst (_ ⊢_↦[ _ - _ ] _ ⨾ _) [Eₚ]xₚ≡ρ[Eₘ]xₘ d
        H″ , array-update , ~ʰ = copy-on-write→in-place H~H d′ (xs [ iFin ]≔ v)
        yₘ≡[Eₘ]xₘ = renVar-inj ρ _ _ (trans (sym [Eₚ]xₚ≡ρyₘ) [Eₚ]xₚ≡ρ[Eₘ]xₘ)
        dₘ′ = subst (_ ⊢_↦[ _ ] _) yₘ≡[Eₘ]xₘ (lookup-𝟘 dₘ)
     in ⟪ H″ , ` xₘ , Eₘ , S ⟫
        red: write₄ₘ iFin v xs dₘ′ array-update ∣S∣≡𝟙
        rel: (remapRen [Eₘ]xₘ ρ , ~ʰ , var [Eₘ]xₘ (sym (renVar-remap-vz ρ [Eₘ]xₘ)) , {! S~S !})
    }
  pure↝mutable free₁             {sₘ = ⟪ H , free arr , E , S ⟫} (ρ , H~H , free arr~arr , S~S) _ =
    _
    red: free₁
    rel: (ρ , H~H , arr~arr , freeₑ ∙ S~S)
  pure↝mutable (free₂ l ∣S∣≡𝟙)    {sₘ = ⟪ H , ` x , E , freeₑ ∙ S ⟫} (ρ , H~H , var [Eₚ]xₚ [Eₚ]xₚ≡ρ[Eₘ]xₘ , freeₑ ∙ S~S) _ =
    let ∣S∣≡𝟙 = subst (_≡ 𝟙) (~S→∣≡∣ S~S) ∣S∣≡𝟙 in
    case ~ʰ-lookup H~H (inj₂ non-trivial) (subst (_ ⊢_↦[ 𝟙 - 𝟙 ] _ ⨾ _) [Eₚ]xₚ≡ρ[Eₘ]xₘ l) of λ { (_ , l′ , H~H) →
    _
    red: free₂ l′ ∣S∣≡𝟙
    rel: (ρ , H~H , star , S~S)
    }

-- corollary : (t : ε ⊢ ℕ)
--           → ∀ {n n′ m m′}
--           → {Γᵤ : Con n} {Γₚ : Con n′}
--             {Δᵤ : Con m} {Δₚ : Con m′}
--           → {Eᵤ : Ren Γᵤ Δᵤ} {Eₚ : Ren Γₚ Δₚ}
--           → {Hᵤ : Heap Γᵤ} {Hₚ : Heap Γₚ}
--           → {vᵤ : Δᵤ ⊢ ℕ} {vₚ : Δₚ ⊢ ℕ}
--           → Value vᵤ
--           → Value vₚ
--           → ⟪ ε , t , ε , ε ⟫ ⇒ᵤ* ⟪ Hᵤ , vᵤ , Eᵤ , ε ⟫
--           → Value vᵤ
--           → ⟪ ε , t , ε , ε ⟫ ⇒ₚ* ⟪ Hₚ , vₚ , Eₚ , ε ⟫
--           × Value vₚ
-- corollary = {!   !}

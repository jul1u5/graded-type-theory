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
  using (𝟙-𝟙≡𝟘)
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

-- s : Supports-subtraction
-- s = subtraction-ok

open import ArrayLang.Usage.Properties {ℓ = lzero} {M = Linearity} 𝕄

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
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (varᵤ v d)       H~H ▸s =
    let _ , _ , d′ = ▸↦→↦[] ok {E = E} (~ʰ-lookup H~H d) ▸s
     in _ , var v (_ , d′) , ~ʰ-trans H~H (update-~ʰ d′)
  ungraded↝pure app₁               H~H ▸s = _ , app₁                     , H~H
  ungraded↝pure app₂ₑ              H~H ▸s = _ , app₂ₑ                    , H~H ∙ _
  ungraded↝pure (app₂ p≢𝟘)         H~H ▸s = _ , app₂ p≢𝟘                 , H~H
  ungraded↝pure (app₃ u)           H~H ▸s = _ , app₃ u                   , H~H ∙ _
  ungraded↝pure suc₁               H~H ▸s = _ , suc₁                     , H~H
  ungraded↝pure (suc₂ t)           H~H ▸s = _ , suc₂ t                   , H~H
  ungraded↝pure box-cong₁          H~H ▸s = _ , box-cong₁                , H~H
  ungraded↝pure (box-cong₂ v)      H~H ▸s = _ , box-cong₂ v              , H~H
  ungraded↝pure prod-cong₁         H~H ▸s = _ , prod-cong₁               , H~H
  ungraded↝pure (prod-cong₂ v₁)    H~H ▸s = _ , prod-cong₂ v₁            , H~H
  ungraded↝pure (prod-cong₃ v₁ v₂) H~H ▸s = _ , prod-cong₃ v₁ v₂         , H~H
  ungraded↝pure unit₁              H~H ▸s = _ , unit₁                    , H~H
  ungraded↝pure unit₂              H~H ▸s = _ , unit₂                    , H~H
  ungraded↝pure box₁               H~H ▸s = _ , box₁                     , H~H
  ungraded↝pure (box₂ v)           H~H ▸s = _ , box₂ v                   , H~H ∙ _
  ungraded↝pure prod₁              H~H ▸s = _ , prod₁                    , H~H
  ungraded↝pure (prod₂ v₁ v₂)      H~H ▸s = _ , prod₂ v₁ v₂              , H~H ∙ _ ∙ _
  ungraded↝pure linearly₁          H~H ▸s = _ , linearly₁                , H~H ∙ lin
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (linearly₂ᵤ k d)   H~H ▸s =
    case ▸linearly→↦[] ok {E = E} (~ʰ-lookup H~H d) ▸s of λ {
    d′ → _ , linearly₂ k d′ , H~H
    }
  ungraded↝pure consume₁        H~H ▸s = _ , consume₁                       , H~H
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (consume₂ᵤ l)        H~H ▸s =
    let H-lin , l′ = ▸↦lin→↦[]lin ok {E = E} (~ʰ-lookup H~H l) ▸s
     in _ , consume₂ {!!} l′ , ~ʰ-trans H~H (update-~ʰ l′)
  ungraded↝pure duplicate₁      H~H ▸s = _ , duplicate₁                     , H~H
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (duplicate₂ᵤ l)      H~H ▸s =
    let H-lin , l′ = ▸↦lin→↦[]lin ok {E = E} (~ʰ-lookup H~H l) ▸s
     in _ , duplicate₂ {!   !} l′ , {! ~ʰ-trans H~H (update-~ʰ l′) !}
  ungraded↝pure new₁              H~H ▸s = _ , new₁                          , H~H
  ungraded↝pure (new₂ s t≡s)      H~H ▸s = _ , new₂ s t≡s                    , H~H
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (new₃ᵤ s d)    H~H ▸s =
    let H-lin , d′ = ▸↦lin→↦[]lin ok {E = E} (~ʰ-lookup H~H d) ▸s
     in H-lin ∙[ 𝟙 ]ₕ array _ , new₃ s {! ▸ !} d′ , ~ʰ-trans H~H (update-~ʰ d′) ∙ _
  ungraded↝pure read₁              H~H ▸s = _ , read₁                        , H~H
  ungraded↝pure (read₂ i t≡i)      H~H ▸s = _ , read₂ i t≡i                  , H~H
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (read₃ᵤ i xs d)    H~H ▸s =
    case ▸↦→↦[] ok {E = E} (~ʰ-lookup H~H d) ▸s of λ { (_ , _ , d′) →
    _ , read₃ i xs {!!} {! d′ !} , H~H
    }
  ungraded↝pure write₁             H~H ▸s = _ , write₁                       , H~H
  ungraded↝pure (write₂ v t≡i)     H~H ▸s = _ , write₂ v t≡i                 , H~H
  ungraded↝pure (write₃ i v t≡v)   H~H ▸s = _ , write₃ i v t≡v               , H~H
  ungraded↝pure {s = ⟪ H , _ , E , _ ⟫} (write₄ᵤ i v xs d) H~H ▸s =
    let o′ = array (xs [ i ]≔ v)
        H-arr , d′ = ▸a↦→a↦[] ok {E = E} (~ʰ-lookup H~H d) ▸s
     in H-arr ∙[ 𝟙 ]ₕ o′ , write₄ₚ i v xs {!!} d′ , ~ʰ-trans H~H (update-~ʰ d′) ∙ o′

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
  pure↝mutable (var {E = Eₚ} {x = xₚ} v (p , d)) {sₘ = ⟪ H , ` xₘ , Eₘ , S ⟫} (ρ , H~H , var [Eₚ]xₚ [Eₚ]xₚ≡ρ[Eₘ]xₘ , S~S) (_ , _ , ▸S , _) =
    let ∣S∣≢𝟘 = subst (_≢ 𝟘) (sym (~S→∣≡∣ S~S)) (▸∣S∣≢𝟘 ▸S) in
    case ~ʰ-lookup′ H~H d ∣S∣≢𝟘 of λ { (H′ , yₘ , value v′ E′ , dₘ , [Eₚ]xₚ≡ρyₘ , refl , H′~H′) →
    let yₘ≡[Eₘ]xₘ = renVar-inj ρ _ _ (trans (sym [Eₚ]xₚ≡ρyₘ) [Eₚ]xₚ≡ρ[Eₘ]xₘ)
        dₘ′ = subst₂ (_ ⊢_↦[-_] value v′ E′ ⨾ _) yₘ≡[Eₘ]xₘ (~S→∣≡∣ S~S) (p , dₘ)
     in ⟪ _ , ⦅ v′ ⦆ᵛ , E′ , S ⟫
        red: (var v′ dₘ′)
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
  pure↝mutable suc₁ {sₘ = ⟪ H , suc t , E , S ⟫} (ρ , H~H , suc t~t , S~S) _ =
    ⟪ H , t , E , sucₑ ∙ S ⟫
    red: suc₁
    rel: (ρ , H~H , t~t , sucₑ ∙ S~S)
  pure↝mutable (suc₂ value-tₚ) {sₘ = ⟪ H , t , E , sucₑ ∙ S ⟫} (ρ , H~H , t~t , sucₑ ∙ S~S) _ =
    let value-t = ~ᵗ-subst-value t~t value-tₚ in
    ⟪ H , suc t , E , S ⟫
    red: suc₂ value-t
    rel: (ρ , H~H , suc t~t , S~S)
  pure↝mutable box-cong₁     {sₘ = ⟪ H , ! t , E , S ⟫} (ρ , H~H , ! t~t , S~S) _ =
    _
    red: box-cong₁
    rel: (ρ , H~H , t~t , !-ₑ ∙ S~S)
  pure↝mutable (box-cong₂ v)     {sₘ = ⟪ H , t , E , !-ₑ ∙ S ⟫} (ρ , H~H , t~t , !-ₑ ∙ S~S) _ =
    let v′ = ~ᵗ-subst-value t~t v in
    ⟪ H , ! t , E , S ⟫
    red: box-cong₂ v′
    rel: (ρ , H~H , ! t~t , S~S)
  pure↝mutable prod-cong₁    {sₘ = ⟪ H , ⟨ t₁ , t₂ ⟩ , E , S ⟫} (ρ , H~H , ⟨ ~₁ , ~₂ ⟩ , S~S) _ =
    _
    red: prod-cong₁
    rel: (ρ , H~H , ~₁ , ⟨-, ~₂ ⟩ₑ ∙ S~S)
  pure↝mutable (prod-cong₂ (_ , v₁))    {sₘ = ⟪ H , t , E , S ⟫} (ρ , H~H , ~₁ , ⟨-, ~₂ ⟩ₑ ∙ S~S) _ =
    _
    red: prod-cong₂ (_ , ~ᵗ-subst-value ~₁ v₁)
    rel: (ρ , H~H , ~₂ , ⟨ ~₁ ,-⟩ₑ ∙ S~S)
  pure↝mutable (prod-cong₃ (_ , v₁) (_ , v₂))   {sₘ = ⟪ H , t , E , S ⟫} (ρ , H~H , ~₂ , ⟨ ~₁ ,-⟩ₑ ∙ S~S) _ =
    _
    red: prod-cong₃ {! _ , ~ᵗ-subst-value ~₁ v₁  !} (_ , ~ᵗ-subst-value ~₂ v₂)
    rel: (ρ , H~H , {!   !} , S~S)
  pure↝mutable unit₁ {sₘ = ⟪ H , let⋆[ t ] u , E , S ⟫} (ρ , H~H , let⋆[ t~t ] u~u , S~S) _ =
    _
    red: unit₁
    rel: (ρ , H~H , t~t , let⋆[-]ₑ u~u ∙ S~S)
  pure↝mutable unit₂ {sₘ = ⟪ H , star , _ , let⋆[-]ₑ u E ∙ S ⟫} (ρ , H~H , star , let⋆[-]ₑ u~u ∙ S~S) _ =
    _
    red: unit₂
    rel: (ρ , H~H , u~u , S~S)
  pure↝mutable box₁ {sₘ = ⟪ H , let![ t ] u , E , S ⟫} (ρ , H~H , let![ t~t ] u~u , S~S) _ =
    _
    red: box₁
    rel: (ρ , H~H , t~t , let![-]ₑ u~u ∙ S~S)
  pure↝mutable (box₂ (_ , v)) {sₘ = ⟪ H , ! _ , E′ , let![-]ₑ u E ∙ S ⟫} (ρ , H~H , ! t~t , let![-]ₑ u~u ∙ S~S) _ =
    _
    red: box₂ (_ , ~ᵗ-subst-value t~t v)
    rel: (liftRen ρ , {! ~ʰ′-extend H~H  !} , {! t~t  !} , ~S-ren1 S~S)
  pure↝mutable prod₁ {sₘ = ⟪ H , let⊗[ t ] u , E , S ⟫} (ρ , H~H , let⊗[ t~t ] u~u , S~S) _ =
    _
    red: prod₁
    rel: (ρ , H~H , t~t , let⊗[-]ₑ u~u ∙ S~S)
  pure↝mutable (prod₂ v₁ v₂) {sₘ = ⟪ H , ⟨ t₁ , t₂ ⟩ , E′ , let⊗[-]ₑ u E ∙ S ⟫} (ρ , H~H , ⟨ ~₁ , ~₂ ⟩ , let⊗[-]ₑ u~u ∙ S~S) _ =
    _
    red: prod₂ (~ᵗ-subst-value ~₁ v₁) (~ᵗ-subst-value ~₂ v₂)
    rel: (liftRen (liftRen ρ) , {!   !} , {!   !} , ~S-ren1 (~S-ren1 S~S))
  pure↝mutable linearly₁ {sₘ = ⟪ H , linearly t , E , S ⟫} (ρ , H~H , linearly t~t , S~S) _ =
    ⟪ H ∙[ 𝟙 ]ₕ lin , t , liftRen E , linearlyₑ vz ∙ ren1ˢ _ S ⟫
    red: linearly₁
    rel: (liftRen ρ , ~ʰ′-extend H~H , t~t , linearlyₑ ∙ ~S-ren1 S~S)
  pure↝mutable (linearly₂ (k , value-k) d) {sₘ = ⟪ H , t , E , linearlyₑ x ∙ S ⟫} (ρ , H~H , t~t , linearlyₑ ∙ S~S) _ =
    let d′ = ~ʰ-lookup H~H refl refl (inj₁ λ ()) d in
    _
    red: linearly₂ (_ , ~ᵗ-subst-value t~t value-k) d′
    rel: (ρ , H~H , t~t , S~S)
  --   {sₘ = ⟪ H , t , E , S ⟫}
  --   red: linearly₂ {! k !} {!d!}
  --   rel: (ρ , H~H , t~t , S~S)
  pure↝mutable consume₁   {sₘ = ⟪ H , t , E , S ⟫} (ρ , H~H , t~t , S~S) ▸s =
    ?
  pure↝mutable (consume₂ ∣S∣≡𝟙 l)   {sₘ = ⟪ H , t , E , S ⟫} (ρ , H~H , t~t , S~S) ▸s =
    ?
  pure↝mutable duplicate₁  {sₘ = ⟪ H , t , E , S ⟫} (ρ , H~H , t~t , S~S) ▸s =
    ?
  pure↝mutable (duplicate₂ ∣S∣≡𝟙 l)  {sₘ = ⟪ H , t , E , S ⟫} (ρ , H~H , t~t , S~S) ▸s =
    ?
  pure↝mutable new₁              {sₘ = ⟪ H , new l s , E , S ⟫} (ρ , H~H , new l~l s~s , S~S) _ =
    ⟪ H , s , E , new₁ₑ l E ∙ S ⟫
    red: new₁
    rel: (( ρ , H~H , s~s , new₁ₑ l~l ∙ S~S ))
  pure↝mutable (new₂ s t≡s)              {sₘ = ⟪ H , t , E′ , new₁ₑ l E ∙ S ⟫} (ρ , H~H , t~t , new₁ₑ l~l ∙ S~S) _ =
    ⟪ H , l , E , new₂ₑ s ∙ S ⟫
    red: new₂ s {! t≡s  !}
    rel: (ρ , H~H , l~l , new₂ₑ ∙ S~S)
  pure↝mutable (new₃ s ∣S∣≡𝟙 d)        {sₘ = ⟪ H , ` x , E , new₂ₑ s ∙ S ⟫} (ρ , H~H , t~t , new₂ₑ ∙ S~S) _ =
    -- case ~ʰ-lookup′ H~H d {!~ᵗ→≡ t~t!} of λ { (H′ , y , lin , d′ , [E]x≡ρy , refl , H′~H′) →
    _ -- ⟪ H′ ∙[ 𝟙 ]ₕ array _ , ` vz , liftRen E , ren1ˢ _ S ⟫
    red: new₃ s {! ∣S∣≡𝟙 !} {!!}
    rel: (liftRen ρ , ~ʰ′-extend {! H~H  !} , var vz refl , ~S-ren1 S~S)
    -- }
  pure↝mutable read₁             {sₘ = ⟪ H , read arr i , E , S ⟫} (ρ , H~H , read arr~arr i~i , S~S) _ =
    ⟪ H , i , E , read₁ₑ arr E ∙ S ⟫
    red: read₁
    rel: (ρ , H~H , i~i , (read₁ₑ arr~arr ∙ S~S))
  pure↝mutable (read₂ i t≡i)         {sₘ = ⟪ H , t , E′ , read₁ₑ arr E ∙ S ⟫} (ρ , H~H , t~t , read₁ₑ arr~arr ∙ S~S) _ =
    ⟪ H , arr , E , read₂ₑ i ∙ S ⟫
    red: read₂ i {! t≡i  !}
    rel: (ρ , H~H , arr~arr , (read₂ₑ ∙ S~S))
  pure↝mutable (read₃ iₚ xs ∣S∣≡𝟙 d)    {sₘ = ⟪ H , ` x , E , read₂ₑ i ∙ S ⟫} (ρ , H~H , var x′ x~x , read₂ₑ ∙ S~S) _ =
    ⟪ H , ⟨ ` x , _ ⟩ , E , S ⟫
    red: read₃ iₚ xs {! ∣S∣≡𝟙 !} {!d!}
    rel: (ρ , H~H , ⟨ var (renVar E x) x~x , ! {!   !} ⟩ , S~S)
  pure↝mutable write₁            {sₘ = ⟪ H , write arr i v , E , S ⟫} (ρ , H~H , write arr~arr i~i v~v , S~S) _ =
    ⟪ H , v , E , write₁ₑ arr i E ∙ S ⟫
    red: write₁
    rel: (ρ , H~H , v~v , (write₁ₑ arr~arr i~i ∙ S~S))
  pure↝mutable (write₂ v t≡v)        {sₘ = ⟪ H , t , E′ , write₁ₑ arr i E ∙ S ⟫} (ρ , H~H , t~t , write₁ₑ arr~arr i~i ∙ S~S) _ =
    _ -- ⟪ H , i , E , write₂ₑ arr v E ∙ S ⟫
    red: write₂ v {! t≡v  !}
    rel: (ρ , H~H , i~i , {!write₂ₑ ?!} ∙ S~S)
  pure↝mutable (write₃ i v t≡v)      {sₘ = ⟪ H , t , E′ , write₂ₑ arr v E ∙ S ⟫} (ρ , H~H , t~t , write₂ₑ arr~arr ∙ S~S) _ =
    _ -- ⟪ H , arr , E , write₃ₑ i v ∙ S ⟫
    red: write₃ i v {! t≡v  !}
    rel: (ρ , H~H , {!arr~arr!} , write₃ₑ ∙ S~S)
  pure↝mutable
    (write₄ₚ {E = Eₚ} {x = xₚ} iFin v xs ∣S∣≡𝟙 d)
    {sₘ = ⟪ H , ` xₘ , Eₘ , write₃ₑ i v ∙ S ⟫}
    (ρ , H~H , var [Eₘ]xₘ [Eₚ]xₚ≡ρ[Eₘ]xₘ , write₃ₑ ∙ S~S)
    ▸s =
    case ~ʰ-lookup′ H~H d non-trivial of λ { (_ , yₘ , array xs , dₘ , [Eₚ]xₚ≡ρyₘ , refl , H′~H′) →
    let d′ = subst (_ ⊢_↦[ _ - _ ] _ ⨾ _) [Eₚ]xₚ≡ρ[Eₘ]xₘ d
        H″ , array-update , ~ʰ = copy-on-write→in-place H~H d′ iFin v
        yₘ≡[Eₘ]xₘ = renVar-inj ρ _ _ (trans (sym [Eₚ]xₚ≡ρyₘ) [Eₚ]xₚ≡ρ[Eₘ]xₘ)
        dₘ′ = subst (_ ⊢_↦[ _ ] _) yₘ≡[Eₘ]xₘ (lookup-𝟘 dₘ)
     in ⟪ H″ , ` xₘ , Eₘ , S ⟫
        red: write₄ₘ iFin v xs dₘ′ array-update
        rel: (remapRen [Eₘ]xₘ ρ , ~ʰ , var [Eₘ]xₘ (sym (renVar-remap-vz ρ [Eₘ]xₘ)) , {!  !})
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

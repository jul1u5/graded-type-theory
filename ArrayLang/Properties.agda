module ArrayLang.Properties where

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
    case ▸↦→↦[] ok {E = E} (~ʰ-lookup H~H d) ▸s of λ {
    (_ , _ , d′) → _ , var v (_ , d′)                   , ~ʰ-trans H~H (update-~ʰ d′)
    }
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
    d′ → _ , linearly₂ k d′             , H~H
    }
  -- ungraded↝pure consume        H~H ▸s = _ , consume                  , H~H
  -- ungraded↝pure duplicate      H~H ▸s = _ , duplicate                , H~H
  ungraded↝pure new₁           H~H ▸s = _ , new₁                           , H~H
  ungraded↝pure (new₂ s)       H~H ▸s = _ , new₂ s                         , H~H
  ungraded↝pure {s = ⟪ _ , _ , E , _ ⟫} (new₃ᵤ s d)    H~H ▸s =
    let H-lin , d′ = ▸↦lin→↦[]lin ok {E = E} (~ʰ-lookup H~H d) ▸s
        -- d″ = (subst (_ ⊢ _ ↦[ 𝟙 -_] lin ⨾ _) (·-identityʳ _) d′)
     in H-lin ∙[ 𝟙 ]ₕ array _ , new₃ s {! !} d′ , ~ʰ-trans H~H (update-~ʰ d′) ∙ _
  ungraded↝pure read₁          H~H ▸s = _ , read₁                          , H~H
  ungraded↝pure (read₂ i)      H~H ▸s = _ , read₂ i                        , H~H
  ungraded↝pure (read₃ i xs d) H~H ▸s = _ , read₃ i xs (~ʰ-lookup H~H d) , H~H
  ungraded↝pure write₁         H~H ▸s = _ , write₁                         , H~H
  ungraded↝pure (write₂ v)     H~H ▸s = _ , write₂ v                       , H~H
  ungraded↝pure (write₃ i v)   H~H ▸s = _ , write₃ i v                     , H~H
  ungraded↝pure {s = ⟪ H , _ , E , _ ⟫} (write₄ᵤ i v xs d) H~H ▸s =
    let o′ = array (xs [ i ]≔ v) in
    case ▸a↦→a↦[] ok {E = E} (~ʰ-lookup H~H d) ▸s of λ {
    (H-arr , d′) →
    H-arr ∙[ 𝟙 ]ₕ o′ , write₄ₚ i v xs {!!} d′ , ~ʰ-trans H~H (update-~ʰ d′) ∙ o′
    }

module _ {- (ok : Supports-subtraction) -} where
  open import ArrayLang.Heap.Equality.UpToRenaming 𝕄 𝟙-𝟙≡𝟘 non-trivial

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
    (sₘ  : State Γₘ Δₘ A B) →
    sₚ ~ˢ sₘ →

    -- ∀ {γ δ η} →
    -- γ ⨾ δ ⨾ η ▸ sₘ →
    sₚ′ ∼ˢ-⇐ sₘ
  pure↝mutable (var {E = Eₚ} {x = xₚ} v (p , d)) ⟪ H , ` xₘ , Eₘ , S ⟫ (ρ , H~H , var [Eₚ]xₚ [Eₚ]xₚ≡ρ[Eₘ]xₘ , S~S) =
    case ~ʰ-lookup′ H~H d {! p≢𝟘 !} of λ { (H′ , yₘ , value v′ E′ , dₘ , [Eₚ]xₚ≡ρyₘ , refl , H′~H′) →
    let yₘ≡[Eₘ]xₘ = renVar-inj ρ _ _ (trans (sym [Eₚ]xₚ≡ρyₘ) [Eₚ]xₚ≡ρ[Eₘ]xₘ)
        dₘ′ = subst₂ (_ ⊢_↦[-_] value v′ E′ ⨾ _) yₘ≡[Eₘ]xₘ (~S→∣≡∣ S~S) (p , dₘ)
     in ⟪ _ , ⦅ v′ ⦆ᵛ , E′ , S ⟫
        red: (var v′ dₘ′)
        rel: (ρ , H′~H′ , ≡→~ᵗ (sym (ren-comp ρ _ ⦅ v ⦆ᵛ)) , S~S)
    }
  pure↝mutable app₁ ⟪ H , t ∘ u   , E , S ⟫ (ρ , H~H , t~t ∘ u~u , S~S) =
    _
    red: app₁
    rel: (ρ , H~H , t~t , (-∘ₑ u~u) ∙ S~S)
  pure↝mutable app₂ₑ ⟪ H , lam _ t , E , (-∘ₑ u) E′ ∙ S ⟫ (ρ , H~H , lam _ t~t , ((-∘ₑ u~u) ∙ S~S)) =
    ⟪ H ∙[ 𝟘 ]ₕ ↯ , t , liftRen E , ren1ˢ _ S ⟫
    red: app₂ₑ
    rel: (liftRen ρ , ? , t~t , ≡→~S (trans (cong (ren1ˢ _) (~S→≡ S~S)) (ren1ˢ-interchange S ρ)))
  -- pure↝mutable (app₂ p≢𝟘) ⟪ H , lam p t , E , (-∘ₑ u) E′ ∙ S ⟫ (ρ , H~H , lam p t~t , ((-∘ₑ u~u) ∙ S~S)) =
  --   ⟪ H , u , E′ , ((_ , lam p t) ∘ₑ-) E ∙ S ⟫
  --   red: app₂ p≢𝟘
  --   rel: (ρ , H~H , u~u , (lam p t~t ∘ₑ-) ∙ S~S)
  -- pure↝mutable (app₃ (uₚ , value-uₚ)) ⟪ H , u , E , ((_ , lam p t) ∘⟨ p ⟩ₑ-) E′ ∙ S ⟫ (ρ , H~H , u~u , ((lam p t~t ∘ₑ-) ∙ S~S)) =
  --   let value-u = unrenValue E (substValue u~u (renValue _ value-uₚ))
  --       H~H = subst (λ ∣S∣ → _ ∙[ _ ]ₕ _ ~ʰ[ _ ] _ ∙[ ∣S∣ · p ]ₕ _) (~S→∣≡∣ S~S) {! ~ʰ-cons value u~u H~H !}
  --    in
  --   ⟪ H ∙[ ∣ S ∣ · p ]ₕ value (u , value-u) E , t , liftRen E′ , ren1ˢ _ S ⟫
  --   red: app₃ (u , value-u)
  --   rel: (liftRen ρ , H~H , t~t , {!!})
  -- pure↝mutable suc₁ ⟪ H , suc t , E , S ⟫ (ρ , H~H , suc t~t , S~S) =
  --   ⟪ H , t , E , sucₑ ∙ S ⟫
  --   red: suc₁
  --   rel: (ρ , H~H , t~t , (sucₑ ∙ S~S))
  -- pure↝mutable (suc₂ value-tₚ) ⟪ H , t , E , sucₑ ∙ S ⟫ (ρ , H~H , t~t , sucₑ ∙ S~S) =
  --   let value-t = unrenValue E (substValue t~t (renValue _ value-tₚ)) in
  --   ⟪ H , suc t , E , S ⟫
  --   red: suc₂ value-t
  --   rel: (ρ , H~H , suc t~t , S~S)
  -- pure↝mutable box-cong₁     ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S) = {!!} -- _ , _ , box-cong₁  , Hₚ~Hₘ
  -- pure↝mutable (box-cong₂ v)     ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S) = {!!} -- _ , _ , box-cong₂  , Hₚ~Hₘ
  -- pure↝mutable prod-cong₁    ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S) = {!!} -- _ , _ , prod-cong₁ , Hₚ~Hₘ
  -- pure↝mutable (prod-cong₂ v₁)    ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S) = {!!} -- _ , _ , prod-cong₂ , Hₚ~Hₘ
  -- pure↝mutable (prod-cong₃ v₁ v₂)    ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S) = {!!} -- _ , _ , prod-cong₃ , Hₚ~Hₘ
  -- pure↝mutable unit₁         ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S) = {!!} -- _ , _ , unit₁      , Hₚ~Hₘ
  -- pure↝mutable unit₂         ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S) = {!!} -- _ , _ , unit₂      , Hₚ~Hₘ
  -- pure↝mutable box₁          ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S) = {!!} -- _ , _ , box₁       , Hₚ~Hₘ
  -- pure↝mutable (box₂ v)          ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S) = {!!} -- _ , _ , box₂       , Hₚ~Hₘ ∙ _ [ _ ]
  -- pure↝mutable prod₁         ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S) = {!!} -- _ , _ , prod₁      , Hₚ~Hₘ
  -- pure↝mutable (prod₂ v₁ v₂)         ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S) = {!!} -- _ , _ , prod₂      , Hₚ~Hₘ ∙ _ [ _ ] ∙ _ [ _ ]
  -- pure↝mutable linearly₁     ⟪ H , linearly t , E , S ⟫ (ρ , H~H , linearly t~t , S~S) =
  --   ⟪ H ∙[ 𝟙 ]ₕ lin , t , liftRen E , linearlyₑ vz ∙ ren1ˢ _ S ⟫
  --   red: linearly₁
  --   rel: (liftRen ρ , H~H ∙ₕ , t~t , linearlyₑ ∙ {!S~S!})
  -- pure↝mutable (linearly₂ (k , k-value) d) ⟪ H , t , E , linearlyₑ x ∙ S ⟫ (ρ , H~H , t~t , linearlyₑ ∙ S~S) =
  --   ⟪ H , t , E , S ⟫
  --   red: linearly₂ {! k !} {!d!}
  --   rel: (ρ , H~H , t~t , S~S)
  -- -- pure↝mutable consume    ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S? --  = _ , _ , consume   , Hₚ~Hₘ
  -- -- pure↝mutable duplicate  ⟪ H , t , E , S ⟫ (ρ , H~H , t~t , S~S? --  = _ , _ , duplicate , Hₚ~Hₘ
  -- pure↝mutable new₁              ⟪ H , new l s , E , S ⟫ (ρ , H~H , new l~l s~s , S~S) =
  --   ⟪ H , s , E , new₁ₑ l E ∙ S ⟫
  --   red: new₁
  --   rel: (( ρ , H~H , s~s , new₁ₑ l~l ∙ S~S ))
  -- pure↝mutable (new₂ s)              ⟪ H , t , E′ , new₁ₑ l E ∙ S ⟫ (ρ , H~H , t~t , new₁ₑ l~l ∙ S~S) =
  --   let s′ = {!!} in
  --   ⟪ H , l , E , new₂ₑ s ∙ S ⟫
  --   red: subst (λ t → ⟪ H , t , E′ , new₁ₑ l E ∙ S ⟫ ⇒ₘ ⟪ H , l , E , new₂ₑ s ∙ S ⟫) {!!} (new₂ s)
  --   rel: (ρ , H~H , l~l , new₂ₑ ∙ S~S)
  -- pure↝mutable (new₃ s d)        ⟪ H , t , E , new₂ₑ s ∙ S ⟫ (ρ , H~H , t~t , new₂ₑ ∙ S~S) =
  --   case ~ʰ[]-lookup[]′ H~H {!~ᵗ→≡ t~t!} d of λ {
  --   (H′ , lin , d′ , lin , H′~H′) →
  --   ⟪ H′ ∙[ 𝟙 ]ₕ array _ , ` vz , liftRen E , ren1ˢ _ S ⟫
  --   red: subst
  --     (λ t → ⟪ H , t , E , new₂ₑ s ∙ S ⟫ ⇒ₘ ⟪ H′ ∙[ 𝟙 ]ₕ _ , ` vz , liftRen E , ren1ˢ ref S ⟫)
  --     {!!}
  --     (new₃ s {!!})
  --   rel: (liftRen ρ , (H′~H′ ∙ₕ) , var vz refl , {!!})
  --   }
  -- pure↝mutable read₁             ⟪ H , read arr i , E , S ⟫ (ρ , H~H , read arr~arr i~i , S~S) =
  --   ⟪ H , i , E , read₁ₑ arr E ∙ S ⟫
  --   red: read₁
  --   rel: (ρ , H~H , i~i , (read₁ₑ arr~arr ∙ S~S))
  -- pure↝mutable (read₂ i)         ⟪ H , t , E′ , read₁ₑ arr E ∙ S ⟫ (ρ , H~H , t~t , read₁ₑ arr~arr ∙ S~S) =
  --   ⟪ H , arr , E , read₂ₑ i ∙ S ⟫
  --   red: {!read₂!}
  --   rel: (ρ , H~H , arr~arr , (read₂ₑ ∙ S~S))
  -- pure↝mutable (read₃ iₚ xs d)    ⟪ H , t , E , read₂ₑ i ∙ S ⟫ (ρ , H~H , t~t , read₂ₑ ∙ S~S) =
  --   ⟪ H , ⟨ t , _ ⟩ , E , S ⟫
  --   red: subst
  --     (λ t → ⟪ H , t , E , read₂ₑ (toNat iₚ) ∙ S ⟫ ⇒ₘ ⟪ H , ⟨ t , _ ⟩ , E , S ⟫)
  --     {!t~t!}
  --     (read₃ iₚ xs {!d!})
  --   rel: (ρ , H~H , ⟨ {!!} , {!!} ⟩ , S~S)
  -- pure↝mutable write₁            ⟪ H , write arr i v , E , S ⟫ (ρ , H~H , write arr~arr i~i v~v , S~S) =
  --   ⟪ H , v , E , write₁ₑ arr i E ∙ S ⟫
  --   red: write₁
  --   rel: (ρ , H~H , v~v , (write₁ₑ arr~arr i~i ∙ S~S))
  -- pure↝mutable (write₂ v)        ⟪ H , t , E′ , write₁ₑ arr i E ∙ S ⟫ (ρ , H~H , t~t , write₁ₑ arr~arr i~i ∙ S~S) =
  --   ⟪ H , i , E , write₂ₑ arr v E ∙ S ⟫
  --   red: subst
  --     (λ t → ⟪ H , t , E′ , write₁ₑ arr i E ∙ S ⟫ ⇒ₘ ⟪ H , i , E , write₂ₑ arr v E ∙ S ⟫)
  --     {!t~t!}
  --     (write₂ v)
  --   rel: (ρ , H~H , i~i , {!write₂ₑ ?!} ∙ S~S)
  -- pure↝mutable (write₃ i v)      ⟪ H , t , E′ , write₂ₑ arr v E ∙ S ⟫ (ρ , H~H , t~t , write₂ₑ arr~arr ∙ S~S) =
  --   ⟪ H , arr , E , write₃ₑ i v ∙ S ⟫
  --   red: subst
  --     (λ t → ⟪ H , t , E′ , write₂ₑ arr v E ∙ S ⟫ ⇒ₘ ⟪ H , arr , E , write₃ₑ i v ∙ S ⟫)
  --     {!t~t!}
  --     (write₃ i v)
  --   rel: (ρ , H~H , {!arr~arr!} , write₃ₑ ∙ S~S)
  pure↝mutable (write₄ₚ {E = Eₚ} {x = xₚ} iFin v xs ∣S∣≡𝟙 d) ⟪ H , ` xₘ , Eₘ , write₃ₑ i v ∙ S ⟫ (ρ , H~H , var [Eₘ]xₘ [Eₚ]xₚ≡ρ[Eₘ]xₘ , write₃ₑ ∙ S~S) =
    case ~ʰ-lookup′ H~H d non-trivial of λ { (_ , yₘ , array xs , dₘ , [Eₚ]xₚ≡ρyₘ , refl , H′~H′) →
    let d′ = subst (_ ⊢_↦[ _ - _ ] _ ⨾ _) [Eₚ]xₚ≡ρ[Eₘ]xₘ d
        H″ , array-update , ~ʰ = copy-on-write→in-place H~H d′ iFin v
        yₘ≡[Eₘ]xₘ = renVar-inj ρ _ _ (trans (sym [Eₚ]xₚ≡ρyₘ) [Eₚ]xₚ≡ρ[Eₘ]xₘ)
        dₘ′ = subst (_ ⊢_↦[ _ ] _) yₘ≡[Eₘ]xₘ (lookup-𝟘 dₘ)
     in ⟪ H″ , ` xₘ , Eₘ , S ⟫
        red: write₄ₘ iFin v xs dₘ′ array-update
        rel: (remapRen [Eₘ]xₘ ρ , ~ʰ , var [Eₘ]xₘ (sym (renVar-remap-vz ρ [Eₘ]xₘ)) , {!  !})
    }
  pure↝mutable = {!!}

corollary : (t : ε ⊢ ℕ)
          → ∀ {n n′ m m′}
          → {Γᵤ : Con n} {Γₚ : Con n′} {Δᵤ : Con m} {Δₚ : Con m′}
          → {Hᵤ : Heap Γᵤ} {Hₚ : Heap Γₚ}
          → {vᵤ : Δᵤ ⊢ ℕ} {vₚ : Δₚ ⊢ ℕ}
          → {Eᵤ : Ren Γᵤ Δᵤ} {Eₚ : Ren Γₚ Δₚ}
          → ⟪ ε , t , ε , ε ⟫ ⇒ᵤ* ⟪ Hᵤ , vᵤ , Eᵤ , ε ⟫
          → Value vᵤ
          → ⟪ ε , t , ε , ε ⟫ ⇒ₚ* ⟪ Hₚ , vₚ , Eₚ , ε ⟫
          × Value vₚ
corollary = {!   !}

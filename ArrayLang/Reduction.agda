open import Graded.Modality
open import Tools.Bool

module ArrayLang.Reduction
  {ℓ} {M : Set ℓ} (𝕄 : Modality M)
  where

open Modality 𝕄

open import Tools.Fin
open import Tools.Nat hiding (_≤_)
open import Tools.Product
open import Tools.Relation
import Tools.PropositionalEquality as PE

open import Function using (case_of_)
open import Data.Fin using () renaming (fromℕ< to fromNat<; toℕ to toNat)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; lookup; _[_]≔_; replicate)

open import ArrayLang.Syntax 𝕄
open import ArrayLang.Heap 𝕄

private
  variable
    m m′ n n′ : Nat
    A A′ B B′ C D : Type
    Γ Γ′ Δ Δ′ Δ₁ Δ₂ : Con _
    t t′ u t₁ t₂ : Γ ⊢ A
    v v₁ v₂ : Γ ⊢ᵥ A
    x : _ ∋ᶜ _
    H H′ : Heap _
    E E′ E″ E‴ E₁ E₂ : Ren _ _
    S S′ : Stack _ _ _
    p q r : M

-- The heap semantics using single step reductions of heap states.
-- The number of free variables and the size of the heap
-- may change in an evaluation step.

data TypeOfSemantics : Set where
  ungraded pure mutable : TypeOfSemantics

data Copying : TypeOfSemantics → Set where
  instance ungraded : Copying ungraded
  instance pure     : Copying pure

data Graded : TypeOfSemantics → Set where
  instance pure    : Graded pure
  instance mutable : Graded mutable

mutual
  _⇒ᵤ_ _⇒ₚ_ _⇒ₘ_ : State Γ Δ A B → State Γ′ Δ′ A′ B → Set ℓ
  _⇒ᵤ_ = _⇒[ ungraded ]_
  _⇒ₚ_ = _⇒[ pure ]_
  _⇒ₘ_ = _⇒[ mutable ]_

  private
    variable
      ι : TypeOfSemantics

  data _⇒[_]_ {B} : State Γ Δ A B → TypeOfSemantics → State Γ′ Δ′ A′ B → Set ℓ where
    varᵤ : {x : Δ ∋ᶜ var A}
         → (v : Δ′ ⊢ᵥ A)
         → H ⊢ renVar E x ↦ value v E′
         → ⟪ H , ` x    , E  , S ⟫
           ⇒ᵤ
           ⟪ H , ⦅ v ⦆ᵛ , E′ , S ⟫

    var : ⦃ Graded ι ⦄
        → {x : Δ ∋ᶜ var A}
        → (v : Δ′ ⊢ᵥ A)
        → H ⊢ renVar E x ↦[- ∣ S ∣ ] value v E′ ⨾ H′
        → ⟪ H  , ` x    , E  , S ⟫
          ⇒[ ι ]
          ⟪ H′ , ⦅ v ⦆ᵛ , E′ , S ⟫

    app₁ : {t : Δ ⊢ A [ p ]⇒ B} {u : Δ ⊢ A}
         → ⟪ H  , t ∘⟨ p ⟩ u ,      E  ,                                S ⟫
           ⇒[ ι ]
           ⟪ H  , t          ,      E  ,              (-∘⟨ p ⟩ₑ u) E  ∙ S ⟫

    -- If the application (and as a result the lambda) has multiplicity 𝟘, we just evaluate the body.
    app₂ₑ : {t : Δ ∙ var A ⊢ B} {u : Δ′ ⊢ A}
         → let H′ = H ∙[ 𝟘 ]ₕ ↯ in
           ⟪ H  , lam 𝟘 t    ,      E′ ,              (-∘⟨ 𝟘 ⟩ₑ u) E  ∙ S ⟫
           ⇒[ ι ]
           ⟪ H′ , t          , liftRen E′ ,                           ren1ˢ _ S ⟫

    -- Alternatively, we evaluate the argument, and then proceed to the body.
    app₂ : {t : Δ ∙ var A ⊢ B} {u : Δ′ ⊢ A}
         → p PE.≢ 𝟘
         → ⟪ H  , lam p t    ,      E′ ,              (-∘⟨ p ⟩ₑ u) E  ∙ S ⟫
           ⇒[ ι ]
           ⟪ H  , u          ,      E  , ((_ , lam p t) ∘⟨ p ⟩ₑ-)  E′ ∙ S ⟫
    app₃ : {t : Δ ∙ var A ⊢ B}
         → (v@(u , _) : Δ′ ⊢ᵥ A)
         → let H′ = H ∙[ ∣ S ∣ · p ]ₕ value v E in
           ⟪ H  , u          ,      E  , ((_ , lam p t) ∘⟨ p ⟩ₑ-)  E′ ∙ S ⟫
           ⇒[ ι ]
           ⟪ H′ , t          , liftRen E′ ,                           ren1ˢ _ S ⟫

    suc₁ : ⟪ H , suc t , E ,        S ⟫
           ⇒[ ι ]
           ⟪ H , t     , E , sucₑ ∙ S ⟫

    suc₂ : {E : Ren Γ Δ}
           {t : Δ ⊢ ℕ}
           (v : Value t)
         → ⟪ H , t     , E , sucₑ ∙ S ⟫
           ⇒[ ι ]
           ⟪ H , suc t , E ,        S ⟫

    box-cong₁ : ⟪ H , ! t , E ,       S ⟫
                ⇒[ ι ]
                ⟪ H , t   , E , !-ₑ ∙ S ⟫
    box-cong₂ : Value t
              → ⟪ H , t   , E , !-ₑ ∙ S ⟫
                ⇒[ ι ]
                ⟪ H , ! t , E ,       S ⟫

    prod-cong₁ : {t₁ : Δ ⊢ A} {t₂ : Δ ⊢ B}
                 {E : Ren Γ Δ}
               → ⟪ H , ⟨ t₁ , t₂ ⟩             , E  ,                S ⟫
                 ⇒[ ι ]
                 ⟪ H , t₁                      , E  , ⟨-, t₂ ⟩ₑ E  ∙ S ⟫
    prod-cong₂ : (v₁ : Δ₁ ⊢ᵥ A) {t₂ : Δ ⊢ B}
                 {E : Ren Γ Δ} {E₁ : Ren Γ Δ₁}
               → ⟪ H , ⦅ v₁ ⦆ᵛ                 , E₁ , ⟨-, t₂ ⟩ₑ E  ∙ S ⟫
                 ⇒[ ι ]
                 ⟪ H , t₂                      , E  , ⟨ v₁ ,-⟩ₑ E₁ ∙ S ⟫
    prod-cong₃ : (v₁@(t₁ , _) : Δ₁ ⊢ᵥ A) (v₂@(t₂ , _) : Δ₂ ⊢ᵥ B)
                 {E₁ : Ren Γ Δ₁} {E₂ : Ren Γ Δ₂}
               → ⟪ H , t₂                      , E₂ , ⟨ v₁ ,-⟩ₑ E₁ ∙ S ⟫
                 ⇒[ ι ]
                 ⟪ H , ⟨ ren E₁ t₁ , ren E₂ t₂ ⟩ , idRen ,                S ⟫
    -- Maybe there's a better way to do this, without the two weakenings

    unit₁ : ⟪ H , let⋆[ t ] u , E ,                S ⟫
            ⇒[ ι ]
            ⟪ H , t           , E , let⋆[-]ₑ u E ∙ S ⟫
    unit₂ : ⟪ H , star        , E , let⋆[-]ₑ u E ∙ S ⟫
            ⇒[ ι ]
            ⟪ H , u           , E ,                S ⟫

    box₁ : ⟪ H  , let![ t ] u , E      ,                 S ⟫
           ⇒[ ι ]
           ⟪ H  , t           , E      , let![-]ₑ u E  ∙ S ⟫
    box₂ : (v : Γ ⊢ᵥ A)
         → let H′ = H ∙[ ω ]ₕ value v E′ in
           ⟪ H  , ! ⦅ v ⦆ᵛ    , E      , let![-]ₑ u E′ ∙ S ⟫
           ⇒[ ι ]
           ⟪ H′ , u           , liftRen E ,            ren1ˢ _ S ⟫

    prod₁ : ⟪ H  , let⊗[ t ] u , E              ,                 S ⟫
            ⇒[ ι ]
            ⟪ H  , t           , E              , let⊗[-]ₑ u E  ∙ S ⟫
    prod₂ : {t₁ : Δ ⊢ A} {t₂ : Δ ⊢ A′}
          → (v₁ : Value t₁) → (v₂ : Value t₂)
          → let H′ = H ∙[ ∣ S ∣ ]ₕ value (t₁ , v₁) E
                       ∙[ ∣ S ∣ ]ₕ value (t₂ , v₂) (stepRen E) in
            ⟪ H  , ⟨ t₁ , t₂ ⟩ , E              , let⊗[-]ₑ u E′ ∙ S ⟫
            ⇒[ ι ]
            ⟪ H′ , u           , liftRen (liftRen E′) ,            ren2ˢ S ⟫

    linearly₁ : {k : Γ ∙ var Lin ⊢ ! A}
              → ⟪ H            , linearly k ,      E ,                       S ⟫
                ⇒[ ι ]
                ⟪ H ∙[ 𝟙 ]ₕ lin , k          , liftRen E , linearlyₑ vz ∙ ren1ˢ _ S ⟫

    -- TODO: This currently doesn't handle weakening of Lin
    --
    -- linearly λ l → let x = 1 in let ⋆ = free (new l s) in x
    -- ε ∙ Lin ⊢ 1 , ε ∙ Lin ∙ array _ ⊩ ε ∙ Lin
    --
    -- let x = 1 in linearly λ l → let ⋆ = free (new l s) in x
    -- ε       ⊢ 1 , ε ∙ Lin ∙ array _ ⊩ ε

    linearly₂ᵤ : (k : Δ ⊢ᵥ ! A)
               → H ⊢ x ↦ lin
               → ⟪ H , ⦅ k ⦆ᵛ , E , linearlyₑ x ∙ S ⟫
                 ⇒ᵤ
                 ⟪ H , ⦅ k ⦆ᵛ , E ,               S ⟫

    linearly₂ : ⦃ Graded ι ⦄
              → (k : Δ ⊢ᵥ ! A)
              → H ⊢ x ↦[ 𝟘 ] lin
              → ⟪ H , ⦅ k ⦆ᵛ , E , linearlyₑ x ∙ S ⟫
                ⇒[ ι ]
                ⟪ H , ⦅ k ⦆ᵛ , E ,               S ⟫

    -- Should we really not reduce l in consume, duplicate and new?
    --
    -- Consider the following:
    --
    --   linearly λ l →
    --     let (l1, l2) = duplicate l
    --         arr = new l1 size
    --         ⋆ = consume (let ⋆ = free arr in l2)
    --      in ! ⋆
    --
    -- Here, we free the array inside the argument of consume.
    -- Freeing an array is a runtime operation since we have to remove the array from the heap.
    -- So, it doesn't seem right to throw away the argument of consume, as we will not free the array.
    -- Maybe this would work fine if we had a garbage collector instead?
    -- !!! But how can we then define the _~ʰ′_ relation?
    --
    -- Also, what if we had freeze?
    --
    --   linearly λ l →
    --     let (l1, l2) = duplicate l
    --         arr = new l1 size
    --         ⋆ = consume (let ! arr' = freeze arr in l2)
    --      in ! ⋆
    -- consume : {l : Γ ⊢ Lin}
    --         → ⟪ H  , consume l , E , S ⟫
    --           ⇒[ ι ]
    --           ⟪ H  , star      , E , S ⟫

    -- consume₁ : {l : Γ ⊢ Lin}
    --          → ⟪ H  , consume l , E ,            S ⟫
    --            ⇒[ ι ]
    --            ⟪ H  , l         , E , consumeₑ ∙ S ⟫
    -- consume₂ : {x : Γ ∋ᶜ var Lin}
    --          → H ⊢ x ↦[ 𝟙 ] lin ⨾ H′
    --          → ⟪ H  , ` x       , E , consumeₑ ∙ S ⟫
    --            ⇒[ ι ]
    --            ⟪ H′ , star      , E ,            S ⟫

    -- duplicate : {l : Γ ⊢ Lin}
    --           → ⟪ H , duplicate l , E , S ⟫
    --             ⇒[ ι ]
    --             ⟪ H , ⟨ l , l ⟩   , E , S ⟫

    -- duplicate₁ : {l : Γ ⊢ Lin}
    --            → ⟪ H            , duplicate l            , E      ,              S ⟫
    --              ⇒[ ι ]
    --              ⟪ H            , l                      , E      , duplicateₑ ∙ S ⟫
    -- duplicate₂ : {x : Γ ∋ᶜ var Lin}
    --            → ⟪ H            , ` x                    , E      , duplicateₑ ∙ S ⟫
    --              ⇒[ ι ]
    --              ⟪ H ∙[ 𝟙 ] lin , ⟨ ren1 (` x) , ` here ⟩ , lift E ,         ren1ˢ S ⟫


    new₁  : {l : Δ ⊢ Lin} {s : Δ ⊢ ℕ}
          → ⟪ H  , new l s ,     E  ,             S ⟫
             ⇒[ ι ]
            ⟪ H  , s       ,     E  , new₁ₑ l E ∙ S ⟫
    new₂  : {l : Δ ⊢ Lin}
          → (s : Nat)
          → ⟪ H  , Nat→⊢ s ,     E′ , new₁ₑ l E ∙ S ⟫
             ⇒[ ι ]
            ⟪ H  , l       ,     E  , new₂ₑ s   ∙ S ⟫

    new₃ᵤ : (s : Nat)
          → H ⊢ renVar E x ↦ lin
          → let H′ = H ∙[ 𝟙 ]ₕ array (replicate s 0) in
            ⟪ H  , ` x    ,      E  , new₂ₑ s   ∙ S ⟫
             ⇒ᵤ
            ⟪ H′ , ` vz , liftRen E  ,      ren1ˢ _ S ⟫

    new₃  : ⦃ Graded ι ⦄
          → (s : Nat)
          → ∣ S ∣ PE.≡ 𝟙
          → H ⊢ renVar E x ↦[ 𝟙 - 𝟙 ] lin ⨾ H′
          → let H″ = H′ ∙[ 𝟙 ]ₕ array (replicate s 0) in
            ⟪ H  , ` x    ,      E , new₂ₑ s   ∙ S ⟫
             ⇒[ ι ]
            ⟪ H″ , ` vz , liftRen E ,      ren1ˢ _ S ⟫

    -- new₁ : {l : Γ ⊢ Lin} {s : Γ ⊢ ℕ}
    --      → ⟪ H  , new l s     , E      ,           S ⟫
    --         ⇒[ ι ]
    --        ⟪ H  , l           , E      , new₁ₑ s ∙ S ⟫
    -- new₂ : {x : Γ ∋ᶜ var Lin} {s : Γ ⊢ ℕ}
    --      → H ⊢ x ↦[ 𝟙 ] lin ⨾ H′
    --      → ⟪ H  , ` x         , E      , new₁ₑ s ∙ S ⟫
    --         ⇒[ ι ]
    --        ⟪ H′ , s           , E      , new₂ₑ   ∙ S ⟫
    -- new₃ : {s : Nat}
    --      → let H′ = H ∙[ 𝟙 ] array (replicate s 0) in
    --        ⟪ H  , ⦅ num s ⦆ᵛ  , E      , new₂ₑ   ∙ S ⟫
    --         ⇒[ ι ]
    --        ⟪ H′ , ` here      , lift E ,      ren1ˢ S ⟫

    read₁ : {arr : Δ ⊢ Arr} {i : Δ ⊢ ℕ}
          → ⟪ H , read arr i                        , E  ,                    S ⟫
            ⇒[ ι ]
            ⟪ H , i                                 , E  , read₁ₑ arr   E   ∙ S ⟫
    read₂ : {arr : Δ ⊢ Arr} (i : Nat)
          → ⟪ H , Nat→⊢ i                           , E′ , read₁ₑ arr   E   ∙ S ⟫
            ⇒[ ι ]
            ⟪ H , arr                               , E  , read₂ₑ     i     ∙ S ⟫
    read₃ : {x : Δ ∋ᶜ ref} (i : Fin n) (xs : Vec Nat n)
          → H ⊢ renVar E x ↦ array xs
          → ⟪ H , ` x                               , E  , read₂ₑ (toNat i) ∙ S ⟫
            ⇒[ ι ]
            ⟪ H , ⟨ ` x , ! fromNat (lookup xs i) ⟩ , E  ,                    S ⟫

    write₁ : {arr : Δ ⊢ Arr} {i : Δ ⊢ ℕ} {v : Δ ⊢ ℕ}
           → ⟪ H  , write arr i v ,      E  ,                             S ⟫
             ⇒[ ι ]
             ⟪ H  , v             ,      E  , write₁ₑ arr        i    E ∙ S ⟫
    write₂ : {arr : Δ ⊢ Arr} {i : Δ ⊢ ℕ} (v : Nat)
           → ⟪ H  , Nat→⊢ v       ,      E′ , write₁ₑ arr        i    E ∙ S ⟫
             ⇒[ ι ]
             ⟪ H  , i             ,      E  , write₂ₑ arr           v E ∙ S ⟫
    write₃ : {arr : Δ ⊢ Arr} (i : Nat) (v : Nat)
           → ⟪ H  , Nat→⊢ i       ,      E′ , write₂ₑ arr           v E ∙ S ⟫
             ⇒[ ι ]
             ⟪ H  , arr           ,      E  , write₃ₑ            i  v   ∙ S ⟫

    write₄ᵤ : {x : Δ ∋ᶜ ref} (i : Fin n) (v : Nat) (xs : Vec Nat n)
            → H ⊢ renVar E x ↦ array xs
            → let H′ = H ∙[ 𝟙 ]ₕ array (xs [ i ]≔ v) in
              ⟪ H  , ` x          ,         E , write₃ₑ     (toNat i) v   ∙ S ⟫
              ⇒ᵤ
              ⟪ H′ , ` vz         , liftRen E ,                      ren1ˢ _ S ⟫

    write₄ₚ : {x : Δ ∋ᶜ ref} (i : Fin n) (v : Nat) (xs : Vec Nat n)
            -- TODO: does 𝟙 - ∣ S ∣ make sense?
            → ∣ S ∣ PE.≡ 𝟙
            → H ⊢ renVar E x ↦[ 𝟙 - 𝟙 ] array xs ⨾ H′
            → let H″ = H′ ∙[ 𝟙 ]ₕ array (xs [ i ]≔ v) in
              ⟪ H  , ` x          ,         E , write₃ₑ     (toNat i) v   ∙ S ⟫
              ⇒ₚ
              ⟪ H″ , ` vz         , liftRen E ,                      ren1ˢ _ S ⟫

    write₄ₘ : {x : Δ ∋ᶜ ref} (i : Fin n) (v : Nat) (xs : Vec Nat n)
            → H ⊢ renVar E x ↦[ 𝟙 ] array xs
            → H ⊢ renVar E x ≔ (xs [ i ]≔ v) ⨾ H′
            → ⟪ H  , ` x          ,         E , write₃ₑ     (toNat i) v   ∙ S ⟫
              ⇒ₘ
              ⟪ H′ , ` x          ,         E ,                             S ⟫

-- Reflexive, transistive closure of the reduction relation

data _⇒[_]*_ (s : State Γ Δ A B) (ι : TypeOfSemantics) : (s′ : State Γ′ Δ′ A′ B) → Set ℓ where
  id : s ⇒[ ι ]* s
  _⇨_ : ∀ {m″ n″} {Γ″ : Con m″} {Δ″ : Con n″} {A″}
          {s′ : State Γ′ Δ′ A′ B} {s″ : State Γ″ Δ″ A″ B}
      → s ⇒[ ι ] s′ → s′ ⇒[ ι ]* s″ → s ⇒[ ι ]* s″

_⇒ᵤ*_ _⇒ₚ*_ _⇒ₘ*_ : State Γ Δ A B → State Γ′ Δ′ A′ B → Set ℓ
_⇒ᵤ*_ = _⇒[ ungraded ]*_
_⇒ₚ*_ = _⇒[ pure ]*_
_⇒ₘ*_ = _⇒[ mutable ]*_


-- _⇨*_ : ∀ {m n m′ n′ m″ n″} {s : State m n} {s′ : State m′ n′} {s″ : State m″ n″}
--      → s ⇒* s′ → s′ ⇒* s″ → s ⇒* s″
-- id ⇨* d′ = d′
-- (x ⇨ d) ⇨* d′ = x ⇨ (d ⇨* d′)


-- data Heap-preserving : {s : State m n} {s′ : State m′ n′} (d : s ⇒* s′) → Set ℓ where
--   id : ∀ {s : State m n} → Heap-preserving (id {s = s})
--   _⇨_ : ∀ {s : State m n} {d : ⟪ H , t′ , E′ , S′ ⟫ ⇒* s} (x : ⟪ H , t , E , S ⟫ ⇒ ⟪ H , t′ , E′ , S′ ⟫)
--       → Heap-preserving d → Heap-preserving (x ⇨ d)

-- let x = ? in linearly λ l → let ... in x

-- H                                  | t   | E                                     | S
-- -----------------------------------|-----|---------------------------------------|-------------------
-- ε ∙[ ω ] 0 ∙[ 𝟙 ] lin ∙[ 𝟘 ] array , ` 2 , ε ∙ ℕ ∙ Lin ∙ ref ⊩ ε ∙ ℕ ∙ Lin ∙ ref , linearly (` 1) ∙ ε
-- var:
-- ε ∙[ ω ] 0 ∙[ 𝟙 ] lin ∙[ 𝟘 ] array , ! 0 , ε ∙ ℕ ∙ Lin ∙ ref ⊩ ε                 , linearly (` 1) ∙ ε
--                                  ε ⊢ ! 0               ε ∙[ ω ] 0 ∙[ 𝟙 ] lin ∙[ 𝟘 ] array ∋ᶜ ` 1
--
--   wkFromVar (` 1) : ε ∙ ℕ ∙ Lin ∙ ref ⊩ ε ∙ ℕ ∙ ref
--
-- linearly₂:
-- ε ∙[ ω ] 0 ∙[ 𝟘 ] lin ∙[ 𝟘 ] array , ! 0 , ε ∙ ℕ ∙ Lin ∙ ref ⊩ ε                 ,                  ε
--
-- -----------------------------------------------------------------------------------------------------
--
-- ε ∙[ ω ] 0 ∙[ 𝟙 ] lin ∙[ 𝟘 ] array , ! 0 , ε ∙ ℕ ∙ Lin ∙ ref ⊩ ε ∙ ℕ ∙ Lin       , linearly (` 1) ∙ ε
--                        ε ∙ ℕ ∙ Lin ⊢ ! 0                                ε ∙ ℕ ∙ Lin ∙ ref ∋ᶜ ` 1
--                                                         wkVar E (` 0) : ε ∙ ℕ ∙ Lin ∙ ref ∋ᶜ ` 1
--       wkFromVar (` 0)    : ε ∙ ℕ ∙ Lin ⊩ ε ∙ ℕ
--                        t : ε ∙ ℕ       ⊢ ! 0
--   wk (wkFromVar (` 0)) t : ε ∙ ℕ ∙ Lin ⊢ ! 0
--
-- linearly₂:
-- ε ∙[ ω ] 0 ∙[ 𝟘 ] lin ∙[ 𝟘 ] array , ! 0 , ε ∙ ℕ ∙ Lin ∙ ref ⊩ ε ∙ ℕ             ,                  ε
--                              ε ∙ ℕ ⊢ ! 0
--
--               wkFromVar (` 1) : ε ∙ ℕ ∙ Lin ∙ ref ⊩ ε ∙ ℕ • ref
--                            E′ :                     ε ∙ ℕ ⊩ ε • ℕ
-- wk (wkFromVar (` 1) • E′) ! 0 : ε ∙ ℕ ∙ Lin ⊢ ! 0
--
-- -----------------------------------------------------------------------------------------------------
--
-- ε ∙[ ω ] 0 ∙[ 𝟙 ] lin ∙[ 𝟘 ] array , ! 0 , ε ∙ ℕ ∙ Lin ∙ ref ⊩ ε ∙ ℕ ∙ Lin ∙ ref , linearly (` 1) ∙ ε
--                  ε ∙ ℕ ∙ Lin ∙ ref ⊢ ! 0                                ε ∙ ℕ ∙ Lin ∙ ref ∋ᶜ ` 1
--                                                         wkVar E (` 0) : ε ∙ ℕ ∙ Lin ∙ ref ∋ᶜ ` 1
--       wkFromVar (` 0)    : ε ∙ ℕ ∙ Lin ∙ ref ⊩ ε ∙ ℕ ∙ ref
--                        t : ε ∙ ℕ       ∙ ref ⊢ ! 0
--   wk (wkFromVar (` 0)) t : ε ∙ ℕ ∙ Lin ∙ ref ⊢ ! 0
--
-- linearly₂:
-- ε ∙[ ω ] 0 ∙[ 𝟘 ] lin ∙[ 𝟘 ] array , ! 0 , ε ∙ ℕ ∙ Lin ∙ ref ⊩ ε ∙ ℕ             ,                  ε
--                              ε ∙ ℕ ⊢ ! 0
--
--               wkFromVar (` 1) : ε ∙ ℕ ∙ Lin ∙ ref ⊩ ε ∙ ℕ • ref
--                            E′ :                     ε ∙ ℕ ⊩ ε • ℕ
-- wk (wkFromVar (` 1) • E′) ! 0 : ε ∙ ℕ ∙ Lin ⊢ ! 0

-- prod-cong
-- ----------------------------------------------------------------------

-- H = {}
-- ⟨ let x = 4 in λ star → x , let y = 1 in λ star → y ⟩
-- E : ε ⊩ ε

-- H = {x↦4}
-- λ star → x
-- E₁ : ε ∙ 𝓐
--    ⊩ ε ∙ 𝓐

-- H = {x↦4, y↦1}
-- λ star → y
-- E₂ : ε ∙ 𝓐 ∙ 𝓑
--    ⊩ ε     ∙ 𝓑

-- H = {x↦4, y↦1}
-- ⟨ λ star → x , star → y ⟩
-- E  : ε ∙ 𝓐 ∙ 𝓑
--    ⊩ ε ∙ 𝓐 ∙ 𝓑

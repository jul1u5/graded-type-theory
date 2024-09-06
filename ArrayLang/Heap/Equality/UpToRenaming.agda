{-# OPTIONS --hidden-argument-puns #-}
open import Graded.Modality
import Graded.Modality.Properties.Subtraction as Subtraction
open import Tools.PropositionalEquality

module ArrayLang.Heap.Equality.UpToRenaming
  {ℓ} {M : Set ℓ}
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (open Subtraction semiring-with-meet)
  (𝟙-𝟙≡𝟘 : 𝟙 - 𝟙 ≡ 𝟘)
  (𝟙≢𝟘 : 𝟙 ≢ 𝟘)
  where

open import Agda.Primitive

open import ArrayLang.Syntax 𝕄
open import ArrayLang.Usage 𝕄
open import ArrayLang.Heap 𝕄
open import ArrayLang.Heap.Properties 𝕄

open import Tools.Empty
open import Tools.Unit
open import Tools.Nat hiding (_≤_)
open import Tools.Fin
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Relation
open import Tools.Function
open import Tools.Reasoning.PropositionalEquality

open import Function.Base using (_$_; _$′_; _∋_)
open import Data.Product using (Σ-syntax; ∄)

private
  variable
    p q r : M
    n m k : Nat
    Γ Γ′ Δ Δ′ : Con _
    A B C : Type
    𝓐 𝓑 𝓒 : ConItem _
    ρ σ E E′ E₁ E₁′ E₂ E₂′ : Ren _ _
    t t′ u u′ t₁ t₁′ t₂ t₂′ t₃ t₃′ : _ ⊢ _
    x y : _ ∋ᶜ _
    -- v v′ v₁ v₁′ v₂ v₂′ v₃ v₃′ : _ ⊢ᵥ _
    H H′ H″ : Heap _
    o o′ : HeapObject _ _

------------------------------------------------------------------------
-- Equality of terms via a weakening

-- We could make the renaming `Ren Γ Δ` a parameter instead of an index,
-- but this would require an additional syntax declaration.

infix 5 _~ᵗ[_]_
data _~ᵗ[_]_ {n m} {Γ : Con n} {Δ : Con m} : Γ ⊢ A → Ren Γ Δ → Δ ⊢ A → Set ℓ where
  var : {ρ : Ren Γ Δ}
        (x : Δ ∋ᶜ 𝓐)
        {x′ : Γ ∋ᶜ 𝓐}
      → x′ ≡ renVar ρ x
      → ` x′ ~ᵗ[ ρ ] ` x

  lam : ∀ p
      → t ~ᵗ[ liftRen ρ ]  t′
      → lam p t ~ᵗ[ ρ ] lam p t′

  _∘_ : t₁      ~ᵗ[ ρ ] t₁′
      →      t₂ ~ᵗ[ ρ ]       t₂′
      → t₁ ∘ t₂ ~ᵗ[ ρ ] t₁′ ∘ t₂′

  zero : zero ~ᵗ[ ρ ] zero
  suc  :     t ~ᵗ[ ρ ] t′
       → suc t ~ᵗ[ ρ ] suc t′

  star : star ~ᵗ[ ρ ] star
  let⋆[_]_ :       t₁      ~ᵗ[ ρ ]       t₁′
           →            t₂ ~ᵗ[ ρ ]             t₂′
           → let⋆[ t₁ ] t₂ ~ᵗ[ ρ ] let⋆[ t₁′ ] t₂′

  !_ :   t ~ᵗ[ ρ ]   t′
     → ! t ~ᵗ[ ρ ] ! t′
  let![_]_ :       t₁      ~ᵗ[ ρ ]       t₁′
           →            t₂ ~ᵗ[ liftRen ρ ]        t₂′
           → let![ t₁ ] t₂ ~ᵗ[ ρ ] let![ t₁′ ] t₂′

  ⟨_,_⟩ :   t₁        ~ᵗ[ ρ ]   t₁′
        →        t₂   ~ᵗ[ ρ ]         t₂′
        → ⟨ t₁ , t₂ ⟩ ~ᵗ[ ρ ] ⟨ t₁′ , t₂′ ⟩
  let⊗[_]_ :      t₁       ~ᵗ[ ρ ]       t₁′
           →            t₂ ~ᵗ[ liftRen (liftRen ρ) ] t₂′
           → let⊗[ t₁ ] t₂ ~ᵗ[ ρ ] let⊗[ t₁′ ] t₂′

  linearly  :          t ~ᵗ[ liftRen ρ ]     t′
            → linearly t ~ᵗ[ ρ ] linearly t′
  consume   :         t ~ᵗ[ ρ ]         t′
            → consume t ~ᵗ[ ρ ] consume t′
  duplicate :           t ~ᵗ[ ρ ]           t′
            → duplicate t ~ᵗ[ ρ ] duplicate t′

  new   :     t₁    ~ᵗ[ ρ ]     t₁′
        →        t₂ ~ᵗ[ ρ ]         t₂′
        → new t₁ t₂ ~ᵗ[ ρ ] new t₁′ t₂′

  read  :      t₁    ~ᵗ[ ρ ]      t₁′
        →         t₂ ~ᵗ[ ρ ]          t₂′
        → read t₁ t₂ ~ᵗ[ ρ ] read t₁′ t₂′

  write :       t₁       ~ᵗ[ ρ ]       t₁′
        →          t₂    ~ᵗ[ ρ ]           t₂′
        →             t₃ ~ᵗ[ ρ ]               t₃′
        → write t₁ t₂ t₃ ~ᵗ[ ρ ] write t₁′ t₂′ t₃′

  free  :      t ~ᵗ[ ρ ]      t′
        → free t ~ᵗ[ ρ ] free t′

~ᵗ→≡ : t ~ᵗ[ ρ ] t′ → t ≡ ren ρ t′
~ᵗ→≡ (var x′ refl)    = refl
~ᵗ→≡ (lam p ~)        = cong (lam p) (~ᵗ→≡ ~)
~ᵗ→≡ (~₁ ∘ ~₂)        = cong₂ _∘_ (~ᵗ→≡ ~₁) (~ᵗ→≡ ~₂)
~ᵗ→≡ zero             = refl
~ᵗ→≡ (suc ~)          = cong suc (~ᵗ→≡ ~)
~ᵗ→≡ star             = refl
~ᵗ→≡ (let⋆[ ~₁ ] ~₂)  = cong₂ let⋆[_]_ (~ᵗ→≡ ~₁) (~ᵗ→≡ ~₂)
~ᵗ→≡ (! ~)            = cong !_        (~ᵗ→≡ ~)
~ᵗ→≡ (let![ ~₁ ] ~₂)  = cong₂ let![_]_ (~ᵗ→≡ ~₁) (~ᵗ→≡ ~₂)
~ᵗ→≡ ⟨ ~₁ , ~₂ ⟩      = cong₂ ⟨_,_⟩    (~ᵗ→≡ ~₁) (~ᵗ→≡ ~₂)
~ᵗ→≡ (let⊗[ ~₁ ] ~₂)  = cong₂ let⊗[_]_ (~ᵗ→≡ ~₁) (~ᵗ→≡ ~₂)
~ᵗ→≡ (linearly ~)     = cong linearly  (~ᵗ→≡ ~)
~ᵗ→≡ (consume ~)      = cong consume   (~ᵗ→≡ ~)
~ᵗ→≡ (duplicate ~)    = cong duplicate (~ᵗ→≡ ~)
~ᵗ→≡ (new ~₁ ~₂)      = cong₂ new      (~ᵗ→≡ ~₁) (~ᵗ→≡ ~₂)
~ᵗ→≡ (read ~₁ ~₂)     = cong₂ read     (~ᵗ→≡ ~₁) (~ᵗ→≡ ~₂)
~ᵗ→≡ (write ~₁ ~₂ ~₃) = cong₃ write    (~ᵗ→≡ ~₁) (~ᵗ→≡ ~₂) (~ᵗ→≡ ~₃)
~ᵗ→≡ (free ~)         = cong free      (~ᵗ→≡ ~)

~ᵗ-refl : ren ρ t ~ᵗ[ ρ ] t
~ᵗ-refl {t = ` x}         = var x refl
~ᵗ-refl {t = lam p _}     = lam p ~ᵗ-refl
~ᵗ-refl {t = _ ∘ _}       = ~ᵗ-refl ∘ ~ᵗ-refl
~ᵗ-refl {t = zero}        = zero
~ᵗ-refl {t = suc _}       = suc ~ᵗ-refl
~ᵗ-refl {t = star}        = star
~ᵗ-refl {t = let⋆[ _ ] _} = let⋆[ ~ᵗ-refl ] ~ᵗ-refl
~ᵗ-refl {t = ! _}         = ! ~ᵗ-refl
~ᵗ-refl {t = let![ _ ] _} = let![ ~ᵗ-refl ] ~ᵗ-refl
~ᵗ-refl {t = ⟨ _ , _ ⟩}   = ⟨ ~ᵗ-refl , ~ᵗ-refl ⟩
~ᵗ-refl {t = let⊗[ _ ] _} = let⊗[ ~ᵗ-refl ] ~ᵗ-refl
~ᵗ-refl {t = linearly _}  = linearly ~ᵗ-refl
~ᵗ-refl {t = consume _}   = consume ~ᵗ-refl
~ᵗ-refl {t = duplicate _} = duplicate ~ᵗ-refl
~ᵗ-refl {t = new _ _}     = new ~ᵗ-refl ~ᵗ-refl
~ᵗ-refl {t = read _ _}    = read ~ᵗ-refl ~ᵗ-refl
~ᵗ-refl {t = write _ _ _} = write ~ᵗ-refl ~ᵗ-refl ~ᵗ-refl
~ᵗ-refl {t = free _}      = free ~ᵗ-refl

≡→~ᵗ : t ≡ ren ρ t′ → t ~ᵗ[ ρ ] t′
≡→~ᵗ refl = ~ᵗ-refl

------------------------------------------------------------------------
-- Equality of values up to weakening

infix 5 _~ᵛ[_]_
_~ᵛ[_]_ : ∀ {n m} {Γ : Con n} {Δ : Con m}
        → Γ ⊢ᵥ A → Ren Γ Δ
        → Δ ⊢ᵥ A → Set ℓ
(t , v) ~ᵛ[ ρ ] (t′ , v′) = t ~ᵗ[ ρ ] t′

substValue : ∀ {n m}
             {Γ : Con n} {Δ : Con m}
             {ρ : Ren Γ Δ}
             {t : Γ ⊢ A} {t′ : Δ ⊢ A}
           → t ~ᵗ[ ρ ] t′ → Value t → Value t′
substValue (var x′ refl) (ref x) = ref x′
substValue (lam p ~)     (lam p t) = lam p _
substValue zero          zero = zero
substValue (suc ~)       (suc v) = suc (substValue ~ v)
substValue star          star  = star
substValue (! ~)         (! v) = ! substValue ~ v
substValue ⟨ ~₁ , ~₂ ⟩   ⟨ v₁ , v₂ ⟩ = ⟨ substValue ~₁ v₁ , substValue ~₂ v₂ ⟩

-- substValue : {}
--              ⦅ v ⦆ᵛ ~ᵗ[ ρ ] t
--            → t ≡ ⦅ v′ ⦆ᵛ
-- substValue {t = t} ~ = {!t ~ !}

private
  variable
    v v′ : _ ⊢ᵥ _

~ᵗ→~ᵛ : ⦅ v ⦆ᵛ ~ᵗ[ ρ ] ⦅ v′ ⦆ᵛ → v ~ᵛ[ ρ ] v′
~ᵗ→~ᵛ ~ = ~

open import Relation.Binary.PropositionalEquality using (cong-app)

~ᵛ→≡ : v ~ᵛ[ ρ ] v′ → v ≡ renᵛ ρ v′
~ᵛ→≡ (var x refl) = {! cong-app _,_  !}
~ᵛ→≡ (lam p ~) = {!   !}
~ᵛ→≡ zero = {!   !}
~ᵛ→≡ (suc ~) = {!   !}
~ᵛ→≡ star = {!   !}
~ᵛ→≡ (! ~) = {!   !}
~ᵛ→≡ ⟨ ~ , ~₁ ⟩ = {!   !} -- refl

~ᵛ-refl : renᵛ ρ v ~ᵛ[ ρ ] v
~ᵛ-refl {v = v , value-v} = {!   !}

≡→∼ᵛ : v ≡ renᵛ ρ v′ → v ~ᵛ[ ρ ] v′
≡→∼ᵛ refl = {! ~ᵛ-refl !}

------------------------------------------------------------------------
-- Elimator equality up to weakening

mutual
  _~ᵉ[_]_ : Elim Γ A B → Ren Γ Δ → Elim Δ A B → Set ℓ
  e ~ᵉ[ ρ ] e′ = _ ∷ e ~ᵉ[ ρ ] e′

  infix 5 _∷_~ᵉ[_]_
  data _∷_~ᵉ[_]_ {Γ : Con n} {Γ′ : Con m}
    : ∀ B
    → Elim Γ A B
    → Ren Γ Γ′
    → Elim Γ′ A B
    → Set ℓ where
    -∘ₑ_ : {u  : Δ ⊢ A} {u′ : Δ′ ⊢ A}
         →           ren E u   ~ᵗ[ ρ ]     ren E′ u′
         → B ∷ (-∘⟨ p ⟩ₑ u) E ~ᵉ[ ρ ] (-∘⟨ p ⟩ₑ u′) E′

    _∘ₑ- : {v  : Δ ⊢ᵥ A [ p ]⇒ B} {v′ : Δ′ ⊢ᵥ A [ p ]⇒ B}
         → renᵛ E v            ~ᵛ[ ρ ]  renᵛ E′ v′
         → B ∷ (v ∘⟨ p ⟩ₑ-) E ~ᵉ[ ρ ] (v′ ∘⟨ p ⟩ₑ-) E′

    sucₑ : sucₑ ~ᵉ[ ρ ] sucₑ

    !-ₑ : ! B ∷ !-ₑ ~ᵉ[ ρ ] !-ₑ

    ⟨-,_⟩ₑ : {u  : Δ  ⊢ B} {E  : Ren Γ Δ}
             {u′ : Δ′ ⊢ B} {E′ : Ren Γ′ Δ′}
           →            ren E u      ~ᵗ[ ρ ] ren E′ u′
           → A ⊗ _ ∷ ⟨-, u ⟩ₑ E ~ᵉ[ ρ ] ⟨-, u′ ⟩ₑ E′
    ⟨_,-⟩ₑ : {v  : Δ  ⊢ᵥ A} {E₁  : Ren Γ Δ}
             {v′ : Δ′ ⊢ᵥ A} {E₁′ : Ren Γ′ Δ′}
             {ρ : Ren Γ Γ′}
           → renᵛ E v            ~ᵛ[ ρ ] renᵛ E′ v′
           → _ ⊗ B ∷ ⟨ v ,-⟩ₑ E ~ᵉ[ ρ ] ⟨ v′ ,-⟩ₑ E′

    let⋆[-]ₑ : {u  : Δ  ⊢ B} {E  : Ren Γ Δ}
               {u′ : Δ′ ⊢ B} {E′ : Ren Γ′ Δ′}
             → ren E u           ~ᵗ[ ρ ] ren E′ u′
             → B ∷ let⋆[-]ₑ u E ~ᵉ[ ρ ] let⋆[-]ₑ u′ E′

    let![-]ₑ : {u  : Δ  ∙ var A ⊢ B} {E  : Ren Γ Δ}
               {u′ : Δ′ ∙ var A ⊢ B} {E′ : Ren Γ′ Δ′}
             → ren (liftRen E) u    ~ᵗ[ liftRen ρ ] ren (liftRen E′) u′
             → B ∷ let![-]ₑ u E ~ᵉ[      ρ ] let![-]ₑ u′ E′

    let⊗[-]ₑ : {u  : Δ  ∙ var A ∙ var B ⊢ C} {E  : Ren Γ Δ}
               {u′ : Δ′ ∙ var A ∙ var B ⊢ C} {E′ : Ren Γ′ Δ′}
             → ren (liftRen (liftRen E)) u ~ᵗ[ liftRen (liftRen ρ) ] ren (liftRen (liftRen E′)) u′
             → C ∷ let⊗[-]ₑ u E     ~ᵉ[             ρ ] let⊗[-]ₑ u′ E′

    linearlyₑ : {x : Γ ∋ᶜ var Lin} {x′ : Γ′ ∋ᶜ var Lin}
              → ! A ∷ linearlyₑ (renVar ρ x′) ~ᵉ[ ρ ] linearlyₑ x′

    consumeₑ : consumeₑ ~ᵉ[ ρ ] consumeₑ
    duplicateₑ : duplicateₑ ~ᵉ[ ρ ] duplicateₑ

    new₁ₑ : ren E t₂    ~ᵗ[ ρ ] ren E′ t₂′
          → new₁ₑ t₂ E ~ᵉ[ ρ ] new₁ₑ t₂′ E′
    new₂ₑ : ∀ {s}
          → new₂ₑ s ~ᵉ[ ρ ] new₂ₑ s

    read₁ₑ : ren E t    ~ᵗ[ ρ ] ren E′ t′
           → read₁ₑ t E ~ᵉ[ ρ ] read₁ₑ t′ E′
    read₂ₑ : ∀ {i}
           → read₂ₑ i ~ᵉ[ ρ ] read₂ₑ i

    write₁ₑ : ren E t₁         ~ᵗ[ ρ ] ren E′ t₁′
            → ren E t₂         ~ᵗ[ ρ ] ren E′ t₂′
            → write₁ₑ t₁ t₂ E ~ᵉ[ ρ ] write₁ₑ t₁′ t₂′ E′
    write₂ₑ : ∀ {v}
            → ren E t₁         ~ᵗ[ ρ ] ren E′ t₁′
            → write₂ₑ t₁ v E  ~ᵉ[ ρ ] write₂ₑ t₁ v E′
    write₃ₑ : ∀ {i v}
            → write₃ₑ i v ~ᵉ[ ρ ] write₃ₑ i v

    freeₑ   : freeₑ ~ᵉ[ ρ ] freeₑ

private
  variable
    e e′ : Elim _ _ _

~ᵉ→≡ : e ~ᵉ[ ρ ] e′
     → e ≡ renᵉ ρ e′
~ᵉ→≡ {ρ = ρ} {e′ = -∘ₑ_ _ E′} (-∘ₑ_ {E = E} ~) = {! ρ !}
~ᵉ→≡ (~ ∘ₑ-) = {!   !}
~ᵉ→≡ sucₑ = refl
~ᵉ→≡ !-ₑ = refl
~ᵉ→≡ ⟨-, x ⟩ₑ = {!   !}
~ᵉ→≡ ⟨ x ,-⟩ₑ = {!   !}
~ᵉ→≡ (let⋆[-]ₑ x) = {!   !}
~ᵉ→≡ (let![-]ₑ x) = {!   !}
~ᵉ→≡ (let⊗[-]ₑ x) = {!   !}
~ᵉ→≡ linearlyₑ = refl
~ᵉ→≡ consumeₑ = refl
~ᵉ→≡ duplicateₑ = refl
~ᵉ→≡ (new₁ₑ x) = {!   !}
~ᵉ→≡ new₂ₑ = refl
~ᵉ→≡ (read₁ₑ x) = {!   !}
~ᵉ→≡ read₂ₑ = refl
~ᵉ→≡ (write₁ₑ x x₁) = {!   !}
~ᵉ→≡ (write₂ₑ x) = {!   !}
~ᵉ→≡ write₃ₑ = refl
~ᵉ→≡ freeₑ = refl

≡→~ᵉ : e ≡ renᵉ ρ e′
     → e ~ᵉ[ ρ ] e′
≡→~ᵉ = {!   !}

~ᵉ→∣≡∣ : {ρ : Ren Γ Γ′} {e : Elim Γ A B} {e′ : Elim Γ′ A B}
       → e ~ᵉ[ ρ ] e′
       → ∣ e ∣ᵉ ≡ ∣ e′ ∣ᵉ
~ᵉ→∣≡∣ (-∘ₑ ~)        = refl
~ᵉ→∣≡∣ (~ ∘ₑ-)        = refl
~ᵉ→∣≡∣ sucₑ           = refl
~ᵉ→∣≡∣ !-ₑ            = refl
~ᵉ→∣≡∣ ⟨-, ~ ⟩ₑ       = refl
~ᵉ→∣≡∣ ⟨ ~ ,-⟩ₑ       = refl
~ᵉ→∣≡∣ (let⋆[-]ₑ ~)   = refl
~ᵉ→∣≡∣ (let![-]ₑ ~)   = refl
~ᵉ→∣≡∣ (let⊗[-]ₑ ~)   = refl
~ᵉ→∣≡∣ linearlyₑ      = refl
~ᵉ→∣≡∣ consumeₑ       = refl
~ᵉ→∣≡∣ duplicateₑ     = refl
~ᵉ→∣≡∣ (new₁ₑ ~)      = refl
~ᵉ→∣≡∣ new₂ₑ          = refl
~ᵉ→∣≡∣ (read₁ₑ ~)     = refl
~ᵉ→∣≡∣ read₂ₑ         = refl
~ᵉ→∣≡∣ (write₁ₑ ~ ~₁) = refl
~ᵉ→∣≡∣ (write₂ₑ ~)    = refl
~ᵉ→∣≡∣ write₃ₑ        = refl
~ᵉ→∣≡∣ freeₑ          = refl

------------------------------------------------------------------------
-- Stack equality up to weakening

data _~S[_]_ {n m} {Γ : Con n} {Δ : Con m}
  : Stack Γ A B
  → Ren Γ Δ
  → Stack Δ A B
  → Set ℓ where
  ε   : (Stack Γ A A ∋ ε) ~S[ ρ ] (Stack Δ A A ∋ ε)
  _∙_ : {e  : Elim Γ A B} {S  : Stack Γ B C}
        {e′ : Elim Δ A B} {S′ : Stack Δ B C}
      → e     ~ᵉ[ ρ ] e′
      →     S ~S[ ρ ]      S′
      → e ∙ S ~S[ ρ ] e′ ∙ S′

~S→≡ : {S : Stack Γ A B} {S′ : Stack Γ′ A B}
       {ρ : Ren Γ Γ′}
     → S ~S[ ρ ] S′
     → S ≡ renˢ ρ S′
~S→≡ = {!!}

≡→~S : {S : Stack Γ A B} {S′ : Stack Γ′ A B}
       {ρ : Ren Γ Γ′}
     → S ≡ renˢ ρ S′
     → S ~S[ ρ ] S′
≡→~S = {!!}

private
  variable
    S S′ : Stack _ _ _

~S→∣≡∣ : S ~S[ ρ ] S′
       → ∣ S ∣ ≡ ∣ S′ ∣
~S→∣≡∣ ε = refl
~S→∣≡∣ (e~e ∙ S~S) = cong₂ _·_ (~S→∣≡∣ S~S) (~ᵉ→∣≡∣ e~e)

------------------------------------------------------------------------
-- Heap object equality up to weakening

open import Data.Vec using (Vec; lookup; _[_]≔_; replicate)

private
  variable
    Γₚ Γₘ : Con _
    xs xs′ : Vec Nat _

data _~ᵒ[_]_ : HeapObject Γₚ 𝓐 → Ren Γₚ Γₘ → HeapObject Γₘ 𝓐 → Set ℓ where
  value : renᵛ E v     ~ᵛ[ ρ ] renᵛ E′ v′
        → value v E   ~ᵒ[ ρ ] value v′ E′
  array : array xs    ~ᵒ[ ρ ] array xs
  lin   : lin         ~ᵒ[ ρ ] lin
  ↯     : (HeapObject Γ (var A) ∋ ↯) ~ᵒ[ ρ ] ↯

------------------------------------------------------------------------
-- Heap equality up to weakening

-- data _~ʰ[_]_ : Heap Γₚ → Ren Γₚ Γₘ → Heap Γₘ → Set ℓ where
--   ~ʰ-nil  : ∀ {ρ} → ε ~ʰ[ ρ ] ε

--   ~ʰ-cons : {Hₚ : Heap Γₚ} {Hₘ : Heap Γₘ} {ρ : Ren Γₚ Γₘ}
--             {oₚ : HeapObject Γₚ 𝓐} {oₘ : HeapObject Γₘ 𝓐}
--           → oₚ ≡ renᵒ ρ oₘ
--           → {σ : Ren (Γₚ ∙ 𝓐) (Γₘ ∙ 𝓐)}
--           → σ ≡ liftRen ρ
--           → Hₚ            ~ʰ[ ρ ] Hₘ
--           → Hₚ ∙[ p ]ₕ oₚ ~ʰ[ σ ] Hₘ ∙[ p ]ₕ oₘ

--   ~ʰ-copy : {Hₚ Hₚ′ : Heap Γₚ} {Hₘ Hₘ′ : Heap Γₘ} {ρ : Ren Γₚ Γₘ}
--             (x : Γₘ ∋ᶜ ref)
--             (lₚ : Hₚ ⊢ renVar ρ x ↦[ 𝟙 - 𝟙 ] array xs ⨾ Hₚ′)
--             (lₘ : Hₘ ⊢ x ≔ xs′ ⨾ Hₘ′)
--           → {σ : Ren (Γₚ ∙ ref) Γₘ}
--           → σ ≡ remapRen x ρ
--           → Hₚ                    ~ʰ[ ρ ] Hₘ
--           → Hₚ′ ∙[ 𝟙 ]ₕ array xs′ ~ʰ[ σ ] Hₘ′

-- infixl 15 _copy:_from:_with:_
-- pattern εₕ = ~ʰ-nil {ρ = ε}
-- pattern _∙ₕ ~ = ~ʰ-cons refl refl ~
-- pattern _copy:_from:_with:_ ~ x lₚ lₘ = ~ʰ-copy x lₚ lₘ refl ~

-- module _ where
--   open Data.Vec
--   _ : ε ∙[ 𝟘 ]ₕ array (0 ∷ [])
--         ∙[ ω ]ₕ value (_ , zero) ε
--         ∙[ 𝟘 ]ₕ array (1 ∷ [])
--         ∙[ 𝟙 ]ₕ array (2 ∷ [])

--       ~ʰ[ ε ∙[ tt ] vz ∙[ tt , tt ] vs vs vz ]

--       ε ∙[ 𝟙 ]ₕ array (2 ∷ [])
--         ∙[ ω ]ₕ value (_ , zero) ε
--   _ = εₕ ∙ₕ ∙ₕ
--       copy: vs vz
--       from: vs[] vz[] 𝟙-𝟙≡𝟘
--       with: vs vz
--       copy: vs vz
--       from: vz[] 𝟙-𝟙≡𝟘
--       with: vs vz

-- _ : ε ∙[ 𝟘 ] array (1 ∷ [])       -- ----+
--       ∙[ 𝟘 ] array (2 ∷ [])       -- --+ |
--       ∙[ ω ] value (_ , zero) ?   --   | |
--       ∙[ 𝟙 ] array (2 ∷ [])       -- <-+ |
--       ∙[ 𝟙 ] array (1 ∷ [])       -- <---+

--       ~ʰ[ vs vs vz ∷ vs vz ∷ vz ∷ [] ]

--     ε ∙[ 𝟙 ] array (1 ∷ [])
--       ∙[ 𝟙 ] array (2 ∷ [])
--       ∙[ ω ] value (_ , zero) ?
-- _ = εₕ ∙ ∙ ∙
--     copy: vs vz             -- array (2 ∷ [])
--     from: vs vz 𝟙-𝟙≡𝟘
--     copy: vs vs vz          -- array (1 ∷ [])
--     from: vs vs vs vz 𝟙-𝟙≡𝟘

------------------------------------------------------------------------
-- Properties of heap equality

-- ~ʰ-refl : H ~ʰ[ idRen ] H
-- ~ʰ-refl {H = ε} = εₕ
-- ~ʰ-refl {H = H ∙[ p ]ₕ o} = ~ʰ-cons (sym (renᵒ-id o)) refl (~ʰ-refl {H = H})

-- •-~ʰ : H ~ʰ[ ρ ] H′ → H′ ~ʰ[ σ ] H″
--      → H ~ʰ[ ρ • σ ] H″
-- •-~ʰ {ρ = ε} {σ = ε} ~ ~ʰ-nil = ~
-- •-~ʰ ~₁ (~₂ ∙ₕ) = •-~ʰ ~₁ {!!}
-- •-~ʰ ~₁ (~ʰ-copy x lₚ lₘ x₁ ~₂) = {!!}

•-remap-id : {ρ : Ren Γ (Δ ∙ 𝓐)}
           → {x : Δ ∋ᶜ 𝓐}
           → ρ • remapRen x idRen ≡ {! remapRen ? x !}
           --             ^^^^^
           --            Ren Δ Θ
           --    ^^^^^^^^^^^^^^^^
           --      Ren (Δ ∙ 𝓐) Θ
           -- ^^^^^^^^^^^^^^^^^^^
           --      Ren Γ Θ
•-remap-id {ρ = ρ} = {!!}

-- -- ~ʰ[]-trans : H₁ ~ʰ[ ρ ] H₂
-- --            → H₂ ~ʰ[ σ ] H₃
-- --            → H₁ ~ʰ[ ρ • σ ] H₃
-- -- ~ʰ[]-trans = {!!}

-- -- update-~ʰ[] : {ρ : Ren Γₚ Γₘ}
-- --               {Hₚ Hₚ′ : Heap Γₚ} {Hₘ Hₘ′ : Heap Γₘ}
-- --               {x : Γₘ ∋ᶜ 𝓐}
-- --               {oₚ : HeapObject Γₚ 𝓐} {oₘ : HeapObject Γₘ 𝓐}
-- --             → Hₚ ~ʰ[ ρ ] Hₘ
-- --             → Hₚ ⊢ renVar ρ x ↦[ q ] oₚ ⨾ Hₚ′
-- --             → Hₘ ⊢         x ↦[ q ] oₘ ⨾ Hₘ′
-- --             → Hₚ′ ~ʰ[ ρ ] Hₘ′
-- -- update-~ʰ[] (H~H ∙array𝟘) dₚ dₘ = {!!}
-- -- update-~ʰ[] (H~H ∙ x) dₚ dₘ = {!!}

-- -- ~ʰ[]-lookup : {Hₚ : Heap Γₚ} {Hₘ : Heap Γₘ} {ρ : Ren Γₚ Γₘ}
-- --               {xₚ : Γₚ ∋ᶜ 𝓐} {xₘ : Γₘ ∋ᶜ 𝓐}
-- --               {oₚ : HeapObject Γₚ 𝓐} {oₘ : HeapObject Γₘ 𝓐}
-- --             → Hₚ ~ʰ[ ρ ] Hₘ
-- --             → xₚ ≡ renVar ρ xₘ
-- --             → oₚ ~ᵒ[ ρ ] oₘ
-- --             → Hₚ ⊢ xₚ ↦ oₚ
-- --             → Hₘ ⊢ xₘ ↦ oₘ
-- -- ~ʰ[]-lookup                                      (H~H ∙array𝟘) refl o~o (there {o = oₚ} d) = ~ʰ[]-lookup H~H refl {!o~o!} d
-- -- ~ʰ[]-lookup {Hₘ = Hₘ ∙[ p ] oₘ′} {xₘ = here}     (H~H ∙ o~o′)  x≡x  o~o here               = {!!}
-- -- ~ʰ[]-lookup {Hₘ = Hₘ ∙[ p ] oₘ′} {xₘ = there xₚ} (H~H ∙ o~o′)  x≡x  o~o (there d)          = {!!}

-- -- ~ʰ[]-lookup[] : {Hₚ Hₚ′ : Heap Γₚ} {Hₘ Hₘ′ : Heap Γₘ} {ρ : Ren Γₚ Γₘ}
-- --                 {xₚ : Γₚ ∋ᶜ 𝓐} {xₘ : Γₘ ∋ᶜ 𝓐}
-- --                 {oₚ : HeapObject Γₚ 𝓐} {oₘ : HeapObject Γₘ 𝓐}
-- --               → Hₚ ~ʰ[ ρ ] Hₘ
-- --               → xₚ ≡ renVar ρ xₘ
-- --               → oₚ ~ᵒ[ ρ ] oₘ
-- --               → Hₚ ⊢ xₚ ↦[ p ] oₚ ⨾ Hₚ′
-- --               → Hₘ ⊢ xₘ ↦[ p ] oₘ ⨾ Hₘ′
-- -- ~ʰ[]-lookup[] {Γₚ = Γₚ ∙ ref} (Hₚ~Hₘ ∙array𝟘)         refl x≡x (there d) = ~ʰ[]-lookup[] Hₚ~Hₘ refl {!!} d
-- -- ~ʰ[]-lookup[] {Hₘ′ = Hₘ′ ∙[ x ] x₁} {xₘ = here} (Hₚ~Hₘ ∙ o~o′) refl o~o (here p-q≡r) = {!here p-q≡r!}
-- -- ~ʰ[]-lookup[] {Γₚ = Γₚ ∙ _} {xₘ = there x} (Hₚ~Hₘ ∙ o~o′) refl o~o (there d) = {!!}

-- -- ~ᵛ• : {ρ : Ren Γ Γ′} {E′ : Ren Γ′ Δ′}
-- --       {v  : Γ  ⊢ᵥ A}
-- --       {v′ : Δ′ ⊢ᵥ A}
-- --     → v ~ᵛ[ ρ      ] renᵛ E′ v′
-- --     → v ~ᵛ[ ρ • E′ ] v′
-- -- ~ᵛ• {v = lam p t}     {lam .p t′}     (lam .p ~)  = lam p {!t~t!}
-- -- ~ᵛ• {v = num n}       {num .n}        (num .n)    = num n
-- -- ~ᵛ• {v = star}        {star}          star        = star
-- -- ~ᵛ• {v = ! v}         { ! v′}         (! ~)       = ! ~ᵛ• ~
-- -- ~ᵛ• {v = ⟨ v₁ , v₂ ⟩} {⟨ v₁′ , v₂′ ⟩} ⟨ ~₁ , ~₂ ⟩ = ⟨ ~ᵛ• ~₁ , ~ᵛ• ~₂ ⟩
-- -- ~ᵛ• {v = ref x}       {ref x′}        (ref ~)   = {!x≡x!}

-- -- ap~ᵛstep : {ρ : Ren Γ Γ′}
-- --            {v  : Δ  ⊢ᵥ A} {E  : Ren Γ Δ}
-- --            {v′ : Γ′ ⊢ᵥ A}
-- --          → renᵛ E v        ~ᵛ[      ρ ] v′
-- --          → renᵛ (step {𝓐 = 𝓐} E) v ~ᵛ[ step {𝓐 = 𝓐} ρ ] v′
-- -- ap~ᵛstep {v′ = lam p x} v~v = {!v~v!}
-- -- ap~ᵛstep {v′ = num x} v~v = {!!}
-- -- ap~ᵛstep {v′ = star} v~v = {!!}
-- -- ap~ᵛstep {v′ = ! v′} v~v = {!!}
-- -- ap~ᵛstep {v′ = ⟨ v′ , v′₁ ⟩} v~v = {!!}
-- -- ap~ᵛstep {v′ = ref x} v~v = {!!}

-- ap~ᵒstep : {ρ : Ren Γ Γ′}
--            {o : HeapObject Γ 𝓐} {o′ : HeapObject Γ′ 𝓐}
--          →               o ~ᵒ[      ρ ] o′
--          → renᵒ (step {𝓐 = 𝓐} id) o ~ᵒ[ step {𝓐 = 𝓐} ρ ] o′
-- ap~ᵒstep (value v~v) = value {! ap~ᵛstep v~v !}
-- ap~ᵒstep array       = array
-- ap~ᵒstep lin         = lin
-- ap~ᵒstep ↯           = ↯

-- ~ʰ[]-lookup[]′ (H~H ∙array𝟘) refl (there d) with ~ʰ[]-lookup[]′ H~H refl d
-- ... | o′ , o~o , d = o′ , {!!} , {!h o~o!} , {!!}
-- ~ʰ[]-lookup[]′ {xₘ = here} (H~H ∙ o~o′) refl (here p-q≡r) = {!here p-q≡r!}
-- ~ʰ[]-lookup[]′ {Γₚ = Γₚ ∙ _} {xₘ = there x} (H~H ∙ o~o′) refl (there d) = {!!}

-- FIXME: It should be possible to write ρ explicitly, without an existential
-- copy-on-write→in-place : {Γ : Con n} {H H′ : Heap Γ} {x : Γ ∋ᶜ ref}
--                        → ∀ {size} → {xs : Vec Nat size} {i : Fin size} {v : Nat}
--                        → H ⊢ x ↦[ p ] array xs ⨾ H′
--                        → ∃ λ H″ → H ⊢ x ≔ (xs [ i ]≔ v) ⨾ H″
--                                 × H′ ∙[ p ]ₕ array (xs [ i ]≔ v) ~ʰ[ remapRen idRen x ] H″
-- copy-on-write→in-place (vz {p} {q} {r} {H} p-q≡r array≡ren-o) =
--   case renᵒ-array (sym array≡ren-o) of λ { refl →
--   H ∙[ p ]ₕ array (_ [ _ ]≔ _) , vz ,
--   ~ʰ-refl copy: vz from: vz p-q≡r array≡ren-o with: vz
--   }
-- copy-on-write→in-place {i} {v} (vs↦′ l array≡ren-o) =
--   case renᵒ-array (sym array≡ren-o) of λ { refl →
--   case copy-on-write→in-place {i = i} {v} l of λ { (H″ , update , ~) →
--   {!!} ∙[ {!!} ]ₕ {!!} , vs update , {!!}
--   }
--   }

update-heap : {Γ : Con m} {H : Heap Γ}
         → {x : Γ ∋ᶜ ref}
         → ∀ {size} → {xs : Vec Nat size}
         → (i : Fin size) (v : Nat)
         → H ⊢ x ↦[ 𝟙 ] array xs
         → ∃ λ H′ → H ⊢ x ≔ (xs [ i ]≔ v) ⨾ H′
update-heap i v (vz[ ren-o≡array ] 𝟙-𝟘≡𝟙) =
  case renᵒ-array ren-o≡array of λ { refl →
    _ , vz
  }
update-heap i v (vs[ ren-o≡array ] l) =
  case renᵒ-array ren-o≡array of λ { refl →
  case update-heap i v l of λ { (H , u) →
    _ , vs u
  }
  }

lookup-𝟘 : H ⊢ x ↦[ p - q ] o ⨾ H′
         → H ⊢ x ↦[ p - 𝟘 ] o ⨾ H
lookup-𝟘 (vz[ ren-o≡ ] p-q≡r) = vz[ ren-o≡ ] p-𝟘≡p
lookup-𝟘 (vs[ ren-o≡ ] l) = vs[ ren-o≡ ] lookup-𝟘 l

data DeadOrAlive (Hₚ : Heap Γₚ) (ρ : Ren Γₚ Γₘ) (Hₘ : Heap Γₘ) (xₚ : Γₚ ∋ᶜ 𝓐) : Set ℓ where
  alive[_⨾_⨾_]↦ₚ_↦ₘ_
    : (xₘ : Γₘ ∋ᶜ 𝓐)
    → renVar ρ xₘ ≡ xₚ
    → {oₘ : HeapObject Γₘ 𝓐}
    → {oₚ : HeapObject Γₚ 𝓐}
    → renᵒ ρ oₘ ≡ oₚ
    → (lₚ : Hₚ ⊢ xₚ ↦[ p ] oₚ)
    → (lₘ : Hₘ ⊢ xₘ ↦[ p ] oₘ)
    → DeadOrAlive Hₚ ρ Hₘ xₚ

  dead
    : (l𝟘 : Hₚ ⊢ xₚ ↦[ 𝟘 ])
    → (∄xₘ : ∀ xₘ → renVar ρ xₘ ≢ xₚ)
    → DeadOrAlive Hₚ ρ Hₘ xₚ

pattern alive↦ₚ_↦ₘ_ lₚ lₘ = alive[_⨾_⨾_]↦ₚ_↦ₘ_ _ refl refl lₚ lₘ
pattern alive[_]↦ₚ_↦ₘ_ xₘ lₚ lₘ = alive[_⨾_⨾_]↦ₚ_↦ₘ_ xₘ refl refl lₚ lₘ

-- Converted from a definition to a record to prevent Agda from eta-expansion
record _~ʰ[_]_ (Hₚ : Heap Γₚ) (ρ : Ren Γₚ Γₘ) (Hₘ : Heap Γₘ) : Set ℓ where
  constructor upToRen
  field
    classify : ∀ {A} {𝓐 : ConItem A}
             → (xₚ : Γₚ ∋ᶜ 𝓐)
             → DeadOrAlive Hₚ ρ Hₘ xₚ

open _~ʰ[_]_

~ʰ′-extend : {Γₚ : Con n} {Γₘ : Con m}
             {Hₚ : Heap Γₚ} {Hₘ : Heap Γₘ}
           → {oₘ : HeapObject Γₘ 𝓐}
           → {ρ : Ren Γₚ Γₘ}
           → Hₚ                   ~ʰ[ ρ ] Hₘ
           → Hₚ ∙[ p ]ₕ renᵒ ρ oₘ ~ʰ[ liftRen ρ ] Hₘ ∙[ p ]ₕ oₘ
~ʰ′-extend ~ .classify vz = alive↦ₚ vz[ renᵒ-interchange _ _ ] p-𝟘≡p ↦ₘ vz[] p-𝟘≡p
~ʰ′-extend {ρ = ρ} ~ .classify (vs xₚ) =
  case ~ .classify xₚ of λ where
    (alive[ xₘ ]↦ₚ lₚ ↦ₘ lₘ) →
      alive[ vs xₘ
           ⨾ renVar-lift-vs ρ xₘ
           ⨾ sym (renᵒ-interchange ρ _)
           ]↦ₚ vs[] lₚ
            ↦ₘ vs[] lₘ
    (dead (o , l𝟘) ∄xₘ) →
      dead
        (ren1ᵒ o , (vs[] l𝟘))
        (λ xₘ [lift-ρ]xₘ≡vs-xₚ →
          case renVar-unlift-vs _ xₘ xₚ [lift-ρ]xₘ≡vs-xₚ of λ { (xₘ′ , refl , ρxₘ′≡xₚ) →
          ∄xₘ xₘ′ ρxₘ′≡xₚ
          })

~ʰ-lookup : {Γₚ : Con n} {Γₘ : Con m}
            {Hₚ : Heap Γₚ} {Hₘ : Heap Γₘ}
            {xₘ : Γₘ ∋ᶜ 𝓐} {xₚ : Γₚ ∋ᶜ 𝓐}
            {ρ : Ren Γₚ Γₘ}
          → Hₚ ~ʰ[ ρ ] Hₘ
          → renVar ρ xₘ ≡ xₚ
          → {oₘ : HeapObject Γₘ 𝓐}
          → {oₚ : HeapObject Γₚ 𝓐}
          → renᵒ ρ oₘ ≡ oₚ
          → p ≢ 𝟘
          → Hₚ ⊢ xₚ ↦[ p ] oₚ
          → Hₘ ⊢ xₘ ↦[ p ] oₘ
~ʰ-lookup {xₚ = xₚ} {ρ = ρ} ~ ρxₘ≡ ρoₘ≡ p≢𝟘 l = case ~ .classify xₚ of λ where
  (alive[ xₘ ]↦ₚ lₚ ↦ₘ lₘ) →
    case renVar-inj ρ _ xₘ ρxₘ≡ of λ { refl →
    case lookup-det l lₚ of λ { (refl , refl , refl) →
    case renᵒ-inj ρ _ _ ρoₘ≡ of λ { refl →
    lₘ
    }
    }
    }
  (dead (o , l𝟘) ∄xₘ) →
    case lookup-det l l𝟘 of λ { (p≡𝟘 , _ , _) →
    ⊥-elim (p≢𝟘 p≡𝟘)
    }

-- - 𝟘 𝟙 ω
-- 𝟘 𝟘 ⊥ ⊥
-- 𝟙 𝟙 𝟘 ⊥
-- ω ω ω ω
--
-- 𝟘   𝟙
--  \ /
--   ω
--
-- ≤ 𝟘 𝟙 ω
-- 𝟘 ⊤ ⊥ ⊥
-- 𝟙 ⊥ ⊤ ⊥
-- ω ⊤ ⊤ ⊤
↦[]→↦[-] : p - q ≡ r
         → H ⊢ x ↦[ p ] o
         → ∃ λ H′
             → H ⊢ x ↦[ p - q ] o ⨾ H′
↦[]→↦[-] p-q≡r (vz[] _) = _ , vz[] p-q≡r
↦[]→↦[-] p-q≡r (vs[] l) = case ↦[]→↦[-] p-q≡r l of λ { (_ , l) → _ , (vs[] l) }

↦[-]→↦[] : H ⊢ x ↦[ p - q ] o ⨾ H′
         → H ⊢ x ↦[ p ] o
↦[-]→↦[] (vz[] _) = vz[] p-𝟘≡p
↦[-]→↦[] (vs[] l) = vs[] ↦[-]→↦[] l

↦[-]→-≡ : H ⊢ x ↦[ p - q ] o ⨾ H′
        → ∃ λ r → p - q ≡ r
↦[-]→-≡ (vz[] p-q≡r) = _ , p-q≡r
↦[-]→-≡ (vs[] l) = ↦[-]→-≡ l

~ʰ-post-lookup : {Γₚ : Con n} {Γₘ : Con m}
                 {ρ : Ren Γₚ Γₘ}
                 {Hₚ Hₚ′ : Heap Γₚ} {Hₘ Hₘ′ : Heap Γₘ}
                 {xₘ : Γₘ ∋ᶜ 𝓐}
                 {oₘ : HeapObject Γₘ 𝓐}
               → Hₚ ~ʰ[ ρ ] Hₘ
               → Hₚ ⊢ renVar ρ xₘ ↦[ p - q ] renᵒ ρ oₘ ⨾ Hₚ′
               → Hₘ ⊢          xₘ ↦[ p - q ]        oₘ ⨾ Hₘ′
               → Hₚ′ ~ʰ[ ρ ] Hₘ′
~ʰ-post-lookup {ρ = ρ} {xₘ = xₘ} ~ lₚ lₘ .classify xₚ =
  case dec-var (renVar ρ xₘ) xₚ of λ where
    (yes (refl , refl , refl)) → case ~ .classify xₚ of λ where
      (alive[ xₘ ⨾ eq ⨾ eq′ ]↦ₚ lₚ ↦ₘ lₘ) → alive[ xₘ ⨾ eq ⨾ eq′ ]↦ₚ {!lₚ!} ↦ₘ {!!}
      (dead l𝟘 ∄xₘ) → {!!}
    (no ≢) → case ~ .classify xₚ of λ where
      (alive[ xₘ ⨾ eq ⨾ eq′ ]↦ₚ lₚ ↦ₘ lₘ) → alive[ xₘ ⨾ eq ⨾ eq′ ]↦ₚ {!lₚ!} ↦ₘ {!!}
      (dead l𝟘 ∄xₘ) → {!!}
-- case ~ xₚ of λ where
--   (alive↦ₚ lₚ ↦ₘ lₘ) → {!!}
--   (dead l𝟘 ∄xₘ) → {!!}

~ʰ-lookup′ : {Γₚ : Con n} {Γₘ : Con m}
             {ρ : Ren Γₚ Γₘ}
             {Hₚ Hₚ′ : Heap Γₚ} {Hₘ : Heap Γₘ}
             {xₚ : Γₚ ∋ᶜ 𝓐}
             {oₚ : HeapObject Γₚ 𝓐}
           → Hₚ ~ʰ[ ρ ] Hₘ
           → Hₚ ⊢ xₚ ↦[ p - q ] oₚ ⨾ Hₚ′
           → p ≢ 𝟘
           → ∃₃ λ (Hₘ′ : Heap Γₘ)
                  (xₘ : Γₘ ∋ᶜ 𝓐)
                  (oₘ : HeapObject Γₘ 𝓐)
                → (Hₘ ⊢ xₘ ↦[ p - q ] oₘ ⨾ Hₘ′)
                × xₚ ≡ renVar ρ xₘ
                × oₚ ≡ renᵒ ρ oₘ
                × Hₚ′ ~ʰ[ ρ ] Hₘ′
~ʰ-lookup′ {xₚ = xₚ} ~ l p≢𝟘 = case ~ .classify xₚ of λ where
  (alive[ xₘ ⨾ refl ⨾ refl ]↦ₚ lₚ ↦ₘ lₘ) →
    case lookup-det (↦[-]→↦[] l) lₚ of λ { (refl , refl , refl) →
    case ↦[]→↦[-] (↦[-]→-≡ l .proj₂) lₘ of λ { (Hₘ′ , lₘ′) →
    Hₘ′ , xₘ , _ , lₘ′ , refl , refl , ~ʰ-post-lookup ~ l lₘ′
    }
    }
  (dead l𝟘 ∄xₘ) → {!!}

post-lookup : p - q ≡ r
            → H  ⊢ x ↦[ p - q ] o ⨾ H′
            → H′ ⊢ x ↦[ r ] o
post-lookup {r = r} p-q≡r (vz[] p-q≡r′) =
  case -≡-functional p-q≡r p-q≡r′ of λ { refl →
  vz[] p-𝟘≡p
  }
post-lookup p-q≡r (vs[] l) = vs[] post-lookup p-q≡r l

post-lookup-≢ : {p′ : M}
              → Distinct x y
              → H  ⊢ x ↦[ p′ - q ] o ⨾ H′
              → H  ⊢ y ↦[ p ] o′
              → H′ ⊢ y ↦[ p ] o′
post-lookup-≢ _   (vz[] _)   (vs[] l-y) = vs[] l-y
post-lookup-≢ _   (vs[] l-x) (vz[] _)   = vz[] p-𝟘≡p
post-lookup-≢ x≢y (vs[] l-x) (vs[] l-y) = vs[] post-lookup-≢ x≢y l-x l-y

post-update : H  ⊢ x ≔ xs ⨾ H′
            → H′ ⊢ x ↦[ 𝟙 ] array xs
post-update vz = vz[] p-𝟘≡p
post-update (vs u) = vs[] post-update u

post-update-≢ : Distinct x y
              → H  ⊢ x ≔ xs ⨾ H′
              → H  ⊢ y ↦[ p ] o′
              → H′ ⊢ y ↦[ p ] o′
post-update-≢ _   vz       (vs[] l-y) = vs[] l-y
post-update-≢ _   (vs l-x) (vz[] _)   = vz[] p-𝟘≡p
post-update-≢ x≢y (vs l-x) (vs[] l-y) = vs[] post-update-≢ x≢y l-x l-y

copy-on-write→in-place : {Γₚ : Con n} {Γₘ : Con m} {Hₚ Hₚ′ : Heap Γₚ} {Hₘ : Heap Γₘ}
                       → {x : Γₘ ∋ᶜ ref} {ρ : Ren Γₚ Γₘ}
                       → ∀ {size} → {xs : Vec Nat size}
                       → Hₚ ~ʰ[ ρ ] Hₘ
                       → Hₚ ⊢ renVar ρ x ↦[ 𝟙 - 𝟙 ] array xs ⨾ Hₚ′
                       → (i : Fin size) (v : Nat)
                       → ∃ λ Hₘ′ → Hₘ ⊢ x ≔ (xs [ i ]≔ v) ⨾ Hₘ′
                                 × Hₚ′ ∙[ 𝟙 ]ₕ array (xs [ i ]≔ v) ~ʰ[ remapRen x ρ ] Hₘ′
copy-on-write→in-place {x = x} {ρ = ρ} ~ l i v =
  case lookup→write l i v of λ { (_ , u) →
  case update-heap i v (~ʰ-lookup ~ refl refl 𝟙≢𝟘 (lookup-𝟘 l)) of λ { (Hₘ′ , u′) →
  Hₘ′ , u′ , upToRen λ where
    vz →
      alive[ x
           ⨾ renVar-remap-vz ρ x
           ⨾ refl
           ]↦ₚ vz[] p-𝟘≡p
            ↦ₘ post-update u′
    (vs xₚ) →
      case dec-var xₚ (renVar ρ x) of λ where
        (no ≢) → case ~ .classify xₚ of λ where
          (alive[ xₘ ⨾ ρxₘ≡xₚ ⨾ ρoₘ≡oₚ ]↦ₚ lₚ ↦ₘ lₘ) →
            alive[ xₘ
                 ⨾ renVar-remap-vs ρ xₘ x xₚ ρxₘ≡xₚ
                    (≢→Distinct xₘ x λ where
                      (refl , refl , refl) → ≢ (refl , refl , sym ρxₘ≡xₚ))
                 ⨾ renᵒ→renᵒ-remap ρ x ρoₘ≡oₚ
                 ]↦ₚ vs[]
                    post-lookup-≢
                      (≢→Distinct (renVar ρ x) xₚ λ where (refl , refl , refl) → ≢ (refl , refl , refl))
                      l lₚ
                  ↦ₘ
                    post-update-≢
                      (≢→Distinct x xₘ λ where (refl , refl , refl) → ≢ (refl , refl , sym ρxₘ≡xₚ))
                      u′ lₘ
          (dead (o , xₚ↦[𝟘]) ∄xₘ) →
            dead
              ( ren1ᵒ o
              , vs[]
                  post-lookup-≢
                    (≢→Distinct (renVar ρ x) xₚ λ where (refl , refl , refl) → ≢ (refl , refl , refl))
                    l xₚ↦[𝟘]
              )
              (λ xₘ [remap-x-ρ]≡vs-xₚ → ∄xₘ xₘ (renVar-unremap-vs ρ xₘ x xₚ [remap-x-ρ]≡vs-xₚ))
        (yes (refl , refl , refl)) → dead
          (array _ , vs[] post-lookup 𝟙-𝟙≡𝟘 l)
          (λ xₘ [remap-x-ρ]xₘ≡vs-ρx → ¬Distinct-refl (renVar ρ x) (renVar-unremap-≢ ρ xₘ x (vs renVar ρ x) [remap-x-ρ]xₘ≡vs-ρx))
  }
  }

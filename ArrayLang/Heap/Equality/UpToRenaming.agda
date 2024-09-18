{-# OPTIONS --hidden-argument-puns #-}
open import Graded.Modality
import Graded.Modality.Properties.Subtraction as Subtraction

module ArrayLang.Heap.Equality.UpToRenaming
  {ℓ} {M : Set ℓ}
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (open Subtraction semiring-with-meet)
  (𝟙-𝟙≡𝟘 : 𝟙 - 𝟙 ≡ 𝟘)
  where

open import Graded.Modality.Properties.Has-well-behaved-zero semiring-with-meet

open import Agda.Primitive

open import ArrayLang.Syntax 𝕄
open import ArrayLang.Usage 𝕄
open import ArrayLang.Heap 𝕄
open import ArrayLang.Heap.Properties 𝕄

open import Tools.Empty
open import Tools.Unit
open import Tools.Bool
open import Tools.Nat hiding (_≤_)
open import Tools.Fin
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Relation
open import Tools.Function
open import Tools.Reasoning.PropositionalEquality
open import Tools.PropositionalEquality

open import Function.Base using (_$_; _$′_; _∋_)
open import Data.Product using (Σ-syntax; ∄)

private
  variable
    p q r : M
    n n′ m m′ k : Nat
    Γ Γ′ Δ Δ′ : Con _
    A B C : Type
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
data _~ᵗ[_]_ {Γ : Con n} {Δ : Con m} : Γ ⊢ A → Ren Γ Δ → Δ ⊢ A → Set ℓ where
  var : {ρ : Ren Γ Δ}
        (x : Δ ∋ᶜ A)
        {x′ : Γ ∋ᶜ A}
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

≡→~ᵗ : t ≡ ren ρ t′ → t ~ᵗ[ ρ ] t′
≡→~ᵗ refl = ~ᵗ-refl

------------------------------------------------------------------------
-- Equality of values up to weakening

infix 5 _~ᵛ[_]_
_~ᵛ[_]_ : {Γ : Con n} {Δ : Con m}
        → Γ ⊢ᵥ A → Ren Γ Δ
        → Δ ⊢ᵥ A → Set ℓ
(t , v) ~ᵛ[ ρ ] (t′ , v′) = t ~ᵗ[ ρ ] t′

substValue : t ~ᵗ[ ρ ] t′ → Value t → Value t′
substValue (lam p ~)     (lam p t) = lam p _
substValue zero          zero = zero
substValue (suc ~)       (suc v) = suc (substValue ~ v)
substValue star          star  = star
substValue (! ~)         (! v) = ! substValue ~ v
substValue ⟨ ~₁ , ~₂ ⟩   ⟨ v₁ , v₂ ⟩ = ⟨ substValue ~₁ v₁ , substValue ~₂ v₂ ⟩
substValue (var x refl)  (ref _) = ref x
substValue (var x refl)  (lin _) = lin x

private
  variable
    v v′ : _ ⊢ᵥ _

~ᵗ→~ᵛ : ⦅ v ⦆ᵛ ~ᵗ[ ρ ] ⦅ v′ ⦆ᵛ → v ~ᵛ[ ρ ] v′
~ᵗ→~ᵛ ~ = ~

~ᵛ-refl : (v : Γ ⊢ᵥ A) → renᵛ ρ v ~ᵛ[ ρ ] v
~ᵛ-refl _ = ~ᵗ-refl

postulate
  ~ᵛ→≡ : v ~ᵛ[ ρ ] v′ → v ≡ renᵛ ρ v′

≡→∼ᵛ : v ≡ renᵛ ρ v′ → v ~ᵛ[ ρ ] v′
≡→∼ᵛ {v′} refl = ~ᵛ-refl v′

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
         → ren E u ~ᵗ[ ρ ] ren E′ u′
         → B ∷ (-∘⟨ p ⟩ₑ u) E ~ᵉ[ ρ ] (-∘⟨ p ⟩ₑ u′) E′

    _∘ₑ- : {v  : Δ ⊢ᵥ A [ p ]⇒ B} {v′ : Δ′ ⊢ᵥ A [ p ]⇒ B}
         → renᵛ E v ~ᵛ[ ρ ] renᵛ E′ v′
         → B ∷ (v ∘⟨ p ⟩ₑ-) E ~ᵉ[ ρ ] (v′ ∘⟨ p ⟩ₑ-) E′

    sucₑ : sucₑ ~ᵉ[ ρ ] sucₑ

    !-ₑ : ! B ∷ !-ₑ ~ᵉ[ ρ ] !-ₑ

    ⟨-,_⟩ₑ : {u  : Δ  ⊢ B} {u′ : Δ′ ⊢ B}
             {E  : Ren Γ Δ} {E′ : Ren Γ′ Δ′}
           → ren E u ~ᵗ[ ρ ] ren E′ u′
           → A ⊗ _ ∷ ⟨-, u ⟩ₑ E ~ᵉ[ ρ ] ⟨-, u′ ⟩ₑ E′
    ⟨_,-⟩ₑ : {v  : Δ  ⊢ᵥ A}
             {v′ : Δ′ ⊢ᵥ A}
             {ρ : Ren Γ Γ′}
           → ren E ⦅ v ⦆ᵛ ~ᵗ[ ρ ] ren E′ ⦅ v′ ⦆ᵛ
           → _ ⊗ B ∷ ⟨ v ,-⟩ₑ E ~ᵉ[ ρ ] ⟨ v′ ,-⟩ₑ E′

    let⋆[-]ₑ : {u : Δ  ⊢ B} {u′ : Δ′ ⊢ B}
               {E : Ren Γ Δ} {E′ : Ren Γ′ Δ′}
             → ren E u          ~ᵗ[ ρ ] ren E′ u′
             → B ∷ let⋆[-]ₑ u E ~ᵉ[ ρ ] let⋆[-]ₑ u′ E′

    let![-]ₑ : {u : Δ  ∙ A ⊢ B} {u′ : Δ′ ∙ A ⊢ B}
               {E : Ren Γ Δ} {E′ : Ren Γ′ Δ′}
             → ren (liftRen E) u    ~ᵗ[ liftRen ρ ] ren (liftRen E′) u′
             → B ∷ let![-]ₑ u E ~ᵉ[      ρ ] let![-]ₑ u′ E′

    let⊗[-]ₑ : {u : Δ  ∙ A ∙ B ⊢ C} {u′ : Δ′ ∙ A ∙ B ⊢ C}
               {E : Ren Γ Δ} {E′ : Ren Γ′ Δ′}
             → ren (liftRen (liftRen E)) u ~ᵗ[ liftRen (liftRen ρ) ] ren (liftRen (liftRen E′)) u′
             → C ∷ let⊗[-]ₑ u E     ~ᵉ[             ρ ] let⊗[-]ₑ u′ E′

    linearlyₑ : {x : Γ ∋ᶜ Lin} {x′ : Γ′ ∋ᶜ Lin}
              → ! A ∷ linearlyₑ (renVar ρ x′) ~ᵉ[ ρ ] linearlyₑ x′

    consumeₑ   : consumeₑ   ~ᵉ[ ρ ] consumeₑ
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
            → write₂ₑ t₁ v E  ~ᵉ[ ρ ] write₂ₑ t₁′ v E′
    write₃ₑ : ∀ {i v}
            → write₃ₑ i v ~ᵉ[ ρ ] write₃ₑ i v

    freeₑ   : freeₑ ~ᵉ[ ρ ] freeₑ

private
  variable
    e e′ : Elim _ _ _

postulate
  ~ᵉ→≡ : e ~ᵉ[ ρ ] e′ → e ≡ renᵉ ρ e′
  ~ᵉ-refl : renᵉ ρ e ~ᵉ[ ρ ] e

≡→~ᵉ : e ≡ renᵉ ρ e′
    → e ~ᵉ[ ρ ] e′
≡→~ᵉ refl = ~ᵉ-refl

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

private
  variable
    S S′ : Stack _ _ _

~S-refl : renˢ ρ S ~S[ ρ ] S
~S-refl {S = ε} = ε
~S-refl {S = e ∙ S} = ~ᵉ-refl ∙ ~S-refl

~S→≡ : S ~S[ ρ ] S′
     → S ≡ renˢ ρ S′
~S→≡ ε = refl
~S→≡ (~e ∙ ~S) = cong₂ _∙_ (~ᵉ→≡ ~e) (~S→≡ ~S)

≡→~S : S ≡ renˢ ρ S′
     → S ~S[ ρ ] S′
≡→~S refl = ~S-refl

~S→∣≡∣ : S ~S[ ρ ] S′
       → ∣ S ∣ ≡ ∣ S′ ∣
~S→∣≡∣ ε = refl
~S→∣≡∣ {S = e ∙ S} {S′ = e′ ∙ S′} (e~e ∙ S~S) with is-linearlyₑ e | is-linearlyₑ e′
... | true  | true  = refl
... | true  | false = {!   !}
... | false | true  = {!   !}
... | false | false = cong₂ _·_ (~S→∣≡∣ S~S) (~ᵉ→∣≡∣ e~e)

------------------------------------------------------------------------
-- Heap object equality up to weakening

open import Data.Vec using (Vec; lookup; _[_]≔_; replicate)

private
  variable
    Γₚ Γₘ : Con _
    xs xs′ : Vec Nat _

data _~ᵒ[_]_ : HeapObject Γₚ A → Ren Γₚ Γₘ → HeapObject Γₘ A → Set ℓ where
  value : renᵛ E v     ~ᵛ[ ρ ] renᵛ E′ v′
        → value v E   ~ᵒ[ ρ ] value v′ E′
  array : array xs    ~ᵒ[ ρ ] array xs
  lin   : lin         ~ᵒ[ ρ ] lin
  ↯     : (HeapObject Γ (A) ∋ ↯) ~ᵒ[ ρ ] ↯

------------------------------------------------------------------------
-- Heap equality up to renaming

data DeadOrShared (Hₚ : Heap Γₚ) (ρ : Ren Γₚ Γₘ) (Hₘ : Heap Γₘ) (xₚ : Γₚ ∋ᶜ A) : Set ℓ where
  shared[_⨾_⨾_]↦ₚ_↦ₘ_
    : (xₘ : Γₘ ∋ᶜ A)
    → renVar ρ xₘ ≡ xₚ
    → {oₘ : HeapObject Γₘ A}
    → {oₚ : HeapObject Γₚ A}
    → renᵒ ρ oₘ ≡ oₚ
    → (lₚ : Hₚ ⊢ xₚ ↦[ p ] oₚ)
    → (lₘ : Hₘ ⊢ xₘ ↦[ p ] oₘ)
    → DeadOrShared Hₚ ρ Hₘ xₚ

  dead
    : A ≡ Arr
    → (l𝟘 : Hₚ ⊢ xₚ ↦[ 𝟘 ])
    → (∄xₘ : ∀ xₘ → renVar ρ xₘ ≢ xₚ)
    → DeadOrShared Hₚ ρ Hₘ xₚ

pattern shared↦ₚ_↦ₘ_ lₚ lₘ = shared[_⨾_⨾_]↦ₚ_↦ₘ_ _ refl refl lₚ lₘ
pattern shared[_]↦ₚ_↦ₘ_ xₘ lₚ lₘ = shared[_⨾_⨾_]↦ₚ_↦ₘ_ xₘ refl refl lₚ lₘ

record _~ʰ[_]_ (Hₚ : Heap Γₚ) (ρ : Ren Γₚ Γₘ) (Hₘ : Heap Γₘ) : Set ℓ where
  constructor upToRen
  field
    classify : (xₚ : Γₚ ∋ᶜ A) → DeadOrShared Hₚ ρ Hₘ xₚ

open _~ʰ[_]_

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

~ʰ-refl : H ~ʰ[ idRen ] H
~ʰ-refl {H = ε} .classify ()
~ʰ-refl {H = H ∙[ p ]ₕ o} .classify vz =
  shared[
    vz ⨾
    renVar-id ⨾
    renᵒ-id (ren1ᵒ o)
  ]↦ₚ vz[] p-𝟘≡p
   ↦ₘ vz[] p-𝟘≡p
~ʰ-refl {H = H ∙[ p ]ₕ o} .classify (vs x) with ~ʰ-refl {H = H} .classify x
... | shared[ xₘ ⨾ refl ⨾ refl ]↦ₚ lₚ ↦ₘ lₘ =
  shared[ vs xₘ ⨾ renVar-step idRen xₘ ⨾ sym (renᵒ-interchange idRen _) ]↦ₚ vs[] lₚ ↦ₘ vs[] lₘ
... | dead refl l𝟘 ∄xₘ = ⊥-elim (∄xₘ x renVar-id)

update-heap : {Γ : Con m} {H : Heap Γ} {x : Γ ∋ᶜ Arr}
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

~ʰ′-extend : {Γₚ : Con n} {Γₘ : Con m}
             {Hₚ : Heap Γₚ} {Hₘ : Heap Γₘ}
           → {oₘ : HeapObject Γₘ A}
           → {ρ : Ren Γₚ Γₘ}
           → Hₚ                   ~ʰ[ ρ ] Hₘ
           → Hₚ ∙[ p ]ₕ renᵒ ρ oₘ ~ʰ[ liftRen ρ ] Hₘ ∙[ p ]ₕ oₘ
~ʰ′-extend ~ .classify vz = shared↦ₚ vz[ renᵒ-interchange _ _ ] p-𝟘≡p ↦ₘ vz[] p-𝟘≡p
~ʰ′-extend {ρ = ρ} ~ .classify (vs xₚ) =
  case ~ .classify xₚ of λ where
    (shared[ xₘ ]↦ₚ lₚ ↦ₘ lₘ) →
      shared[ vs xₘ
           ⨾ renVar-lift-vs ρ xₘ
           ⨾ sym (renᵒ-interchange ρ _)
           ]↦ₚ vs[] lₚ
            ↦ₘ vs[] lₘ
    (dead refl (o , l𝟘) ∄xₘ) →
      dead
        refl
        (ren1ᵒ o , (vs[] l𝟘))
        (λ xₘ [lift-ρ]xₘ≡vs-xₚ →
          case renVar-unlift-vs _ xₘ xₚ [lift-ρ]xₘ≡vs-xₚ of λ { (xₘ′ , refl , ρxₘ′≡xₚ) →
          ∄xₘ xₘ′ ρxₘ′≡xₚ
          })

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

module _ ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ where
  ~ʰ-post-lookup : {Γₚ : Con n} {Γₘ : Con m}
                  {ρ : Ren Γₚ Γₘ}
                  {Hₚ Hₚ′ : Heap Γₚ} {Hₘ Hₘ′ : Heap Γₘ}
                  {xₘ : Γₘ ∋ᶜ A}
                  {oₘ : HeapObject Γₘ A}
                → Hₚ ~ʰ[ ρ ] Hₘ
                → Hₚ ⊢ renVar ρ xₘ ↦[ p - q ] renᵒ ρ oₘ ⨾ Hₚ′
                → Hₘ ⊢          xₘ ↦[ p - q ]        oₘ ⨾ Hₘ′
                → Hₚ′ ~ʰ[ ρ ] Hₘ′
  ~ʰ-post-lookup {ρ = ρ} {xₘ = xₘ} ~ lₚ lₘ .classify xₚ =
    case dec-var (renVar ρ xₘ) xₚ of λ where
      (yes (refl , refl)) → case ~ .classify xₚ of λ where
        (shared[ yₘ ⨾ ρyₘ≡ρxₘ ⨾ refl ]↦ₚ yₘ↦ ↦ₘ ρyₘ↦) →
          case renVar-inj ρ _ _ ρyₘ≡ρxₘ of λ { refl →
          case ↦[-]→-≡ lₚ of λ { (_ , p-q≡r) →
          shared↦ₚ post-lookup p-q≡r lₚ ↦ₘ post-lookup p-q≡r lₘ
          }
          }
        (dead refl (_ , l𝟘) ∄xₘ) →
          case lookup-det𝟘 l𝟘 lₚ of λ { (refl , refl , refl , refl) →
          dead refl (_ , post-lookup p-𝟘≡p lₚ) ∄xₘ
          }
      (no ≢) → case ~ .classify xₚ of λ where
        (shared[ yₘ ⨾ refl ⨾ refl ]↦ₚ yₘ↦ ↦ₘ ρyₘ↦) →
          shared↦ₚ post-lookup-≢ (≢→Distinct (renVar ρ xₘ) (renVar ρ yₘ) ≢) lₚ yₘ↦
                ↦ₘ post-lookup-≢ (≢→Distinct xₘ yₘ (λ where (refl , refl) → ≢ (refl , refl))) lₘ ρyₘ↦
        (dead refl (_ , l𝟘) ∄xₘ) → dead refl (_ , post-lookup-≢ (≢→Distinct (renVar ρ xₘ) xₚ (λ where (refl , refl) → ∄xₘ xₘ refl) ) lₚ l𝟘) ∄xₘ

  ~ʰ-lookup : {Hₚ Hₚ′ : Heap Γₚ} {Hₘ : Heap Γₘ}
              {ρ : Ren Γₚ Γₘ}
              {xₘ : Γₘ ∋ᶜ A}
            → Hₚ ~ʰ[ ρ ] Hₘ
            → {oₘ : HeapObject Γₘ A}
            → (A ≢ Arr ⊎ p ≢ 𝟘)
            → Hₚ ⊢ renVar ρ xₘ ↦[ p - q ] renᵒ ρ oₘ ⨾ Hₚ′
            → ∃ λ Hₘ′ → Hₘ ⊢ xₘ ↦[ p - q ] oₘ ⨾ Hₘ′
                      × Hₚ′ ~ʰ[ ρ ] Hₘ′
  ~ʰ-lookup {ρ} {xₘ} ~ A≢Arr⊎p≢𝟘 l = case ~ .classify (renVar ρ xₘ) of λ where
    (shared[ xₘ′ ⨾ ρxₘ≡ ⨾ ρoₘ≡ ]↦ₚ lₚ ↦ₘ lₘ) →
      case renVar-inj ρ _ xₘ ρxₘ≡ of λ { refl →
      case lookup-det (↦[-]→↦[] l) lₚ of λ { (refl , refl , refl) →
      case renᵒ-inj ρ _ _ ρoₘ≡ of λ { refl →
      case ↦[]→↦[-] (↦[-]→-≡ l .proj₂) lₘ of λ { (Hₘ′ , lₘ′) →
      Hₘ′ , lₘ′ , ~ʰ-post-lookup ~ l lₘ′
      }
      }
      }
      }
    (dead A≡Arr (o , l𝟘) ∄xₘ) →
      case A≢Arr⊎p≢𝟘 of λ where
        (inj₁ A≢Arr) →
          ⊥-elim (A≢Arr A≡Arr)
        (inj₂ p≢𝟘) →
          let p≡𝟘 , _ = lookup-det (↦[-]→↦[] l) l𝟘
          in ⊥-elim (p≢𝟘 p≡𝟘)

  ~ʰ-lookup′ : {Γₚ : Con n} {Γₘ : Con m}
              {ρ : Ren Γₚ Γₘ}
              {Hₚ Hₚ′ : Heap Γₚ} {Hₘ : Heap Γₘ}
              {xₚ : Γₚ ∋ᶜ A}
              {oₚ : HeapObject Γₚ A}
            → Hₚ ~ʰ[ ρ ] Hₘ
            → Hₚ ⊢ xₚ ↦[ p - q ] oₚ ⨾ Hₚ′
            → q ≢ 𝟘
            → ∃₃ λ (Hₘ′ : Heap Γₘ)
                    (xₘ : Γₘ ∋ᶜ A)
                    (oₘ : HeapObject Γₘ A)
                  → (Hₘ ⊢ xₘ ↦[ p - q ] oₘ ⨾ Hₘ′)
                  × xₚ ≡ renVar ρ xₘ
                  × oₚ ≡ renᵒ ρ oₘ
                  × Hₚ′ ~ʰ[ ρ ] Hₘ′
  ~ʰ-lookup′ {xₚ = xₚ} ~ l q≢𝟘 = case ~ .classify xₚ of λ where
    (shared[ xₘ ⨾ refl ⨾ refl ]↦ₚ lₚ ↦ₘ lₘ) →
      case lookup-det (↦[-]→↦[] l) lₚ of λ { (refl , refl , refl) →
      case ↦[]→↦[-] (↦[-]→-≡ l .proj₂) lₘ of λ { (Hₘ′ , lₘ′) →
      Hₘ′ , xₘ , _ , lₘ′ , refl , refl , ~ʰ-post-lookup ~ l lₘ′
      }
      }
    (dead refl (_ , l𝟘) ∄xₘ) →
      let p≡𝟘 , _ = lookup-det (↦[-]→↦[] l) l𝟘
          r , p-q≡r = ↦[-]→-≡ l
      in ⊥-elim (𝟘-q≢p q≢𝟘 (subst (_- _ ≡ r) p≡𝟘 p-q≡r))

  copy-on-write→in-place : {Hₚ Hₚ′ : Heap Γₚ} {Hₘ : Heap Γₘ}
                        → {x : Γₘ ∋ᶜ Arr}
                        → ∀ {size} → {xs : Vec Nat size}
                        → Hₚ ~ʰ[ ρ ] Hₘ
                        → Hₚ ⊢ renVar ρ x ↦[ 𝟙 - 𝟙 ] array xs ⨾ Hₚ′
                        → (i : Fin size) (v : Nat)
                        → ∃ λ Hₘ′ → Hₘ ⊢ x ≔ (xs [ i ]≔ v) ⨾ Hₘ′
                                  × Hₚ′ ∙[ 𝟙 ]ₕ array (xs [ i ]≔ v) ~ʰ[ remapRen x ρ ] Hₘ′
  copy-on-write→in-place {ρ} {x} ~ l i v =
    case lookup→write l i v of λ { (_ , u) →
    case ~ʰ-lookup ~ (inj₂ non-trivial) (lookup-𝟘 l) of λ { (_ , l′ , _) →
    case update-heap i v (↦[-]→↦[] l′) of λ { (Hₘ′ , u′) →
    Hₘ′ , u′ , upToRen λ where
      vz →
        shared[ x
            ⨾ renVar-remap-vz ρ x
            ⨾ refl
            ]↦ₚ vz[] p-𝟘≡p
              ↦ₘ post-update u′
      (vs xₚ) →
        case dec-var xₚ (renVar ρ x) of λ where
          (no ≢) → case ~ .classify xₚ of λ where
            (shared[ xₘ ⨾ ρxₘ≡xₚ ⨾ ρoₘ≡oₚ ]↦ₚ lₚ ↦ₘ lₘ) →
              shared[ xₘ
                  ⨾ renVar-remap-vs ρ xₘ x xₚ ρxₘ≡xₚ
                      (≢→Distinct xₘ x λ where
                        (refl , refl) → ≢ (refl , sym ρxₘ≡xₚ))
                  ⨾ {! renᵒ→renᵒ-remap ρ x ρoₘ≡oₚ !}
                  ]↦ₚ vs[]
                      post-lookup-≢
                        (≢→Distinct (renVar ρ x) xₚ λ where (refl , refl) → ≢ (refl , refl))
                        l lₚ
                    ↦ₘ
                      post-update-≢
                        (≢→Distinct x xₘ λ where (refl , refl) → ≢ (refl , sym ρxₘ≡xₚ))
                        u′ lₘ
            (dead refl (o , xₚ↦[𝟘]) ∄xₘ) →
              dead
                refl
                ( ren1ᵒ o
                , vs[]
                    post-lookup-≢
                      (≢→Distinct (renVar ρ x) xₚ λ where (refl , refl) → ≢ (refl , refl))
                      l xₚ↦[𝟘]
                )
                (λ xₘ [remap-x-ρ]≡vs-xₚ → ∄xₘ xₘ (renVar-unremap-vs ρ xₘ x xₚ [remap-x-ρ]≡vs-xₚ))
          (yes (refl , refl)) →
            dead
              refl
              (array _ , vs[] post-lookup 𝟙-𝟙≡𝟘 l)
              (λ xₘ [remap-x-ρ]xₘ≡vs-ρx →
                ¬Distinct-refl
                  (renVar ρ x)
                  (renVar-unremap-≢ ρ xₘ x (vs renVar ρ x) [remap-x-ρ]xₘ≡vs-ρx))
    }
    }
    }

  ~S-ren1 : S ~S[ ρ ] S′ → ren1ˢ A S ~S[ liftRen ρ ] ren1ˢ A S′
  ~S-ren1 {ρ} {S′} S~S = ≡→~S (trans (cong (ren1ˢ _) (~S→≡ S~S)) (ren1ˢ-interchange S′ ρ))

  private
    variable
      Δₚ Δₘ : Con _
      Hₚ Hₘ : Heap _
      Sₚ Sₘ : Stack _ _ _
      tₚ tₘ : _ ⊢ _
      value-tₚ value-tₘ : Value _
      Eₚ Eₘ : Ren _ _

  ~ᵗ-sym : ren σ t ~ᵗ[ ρ ] t′
         → ren ρ t′ ~ᵗ[ σ ] t
  ~ᵗ-sym ~ = ≡→~ᵗ (sym (~ᵗ→≡ ~))

  ~ᵗ-subst-value : ren Eₚ tₚ ~ᵗ[ ρ ] ren Eₘ tₘ
                 → Value tₚ
                 → Value tₘ
  ~ᵗ-subst-value {Eₚ} {Eₘ} ~ v = unrenValue Eₘ (substValue ~ (renValue Eₚ v))

  ~ᵗ-subst-¬value : ren Eₚ tₚ ~ᵗ[ ρ ] ren Eₘ tₘ
                  → ¬ (Value tₚ)
                  → ¬ (Value tₘ)
  ~ᵗ-subst-¬value {Eₚ} {Eₘ} ~ ¬value-tₚ value-tₘ = ¬value-tₚ (substValue (~ᵗ-sym ~) (renValue _ (renValue Eₘ value-tₘ)))

  ~ʰ-cons-value : {tₚ : Δₚ ⊢ A} {tₘ : Δₘ ⊢ A}
                → Hₚ ~ʰ[ ρ ] Hₘ
                → (t~t : ren Eₚ tₚ ~ᵗ[ ρ ] ren Eₘ tₘ)
                → (vₚ : Value tₚ)
                → Sₚ ~S[ ρ ] Sₘ
                → (Hₚ ∙[ ∣ Sₚ ∣ · p ]ₕ value (tₚ , vₚ) Eₚ)
                    ~ʰ[ liftRen ρ ]
                  (Hₘ ∙[ ∣ Sₘ ∣ · p ]ₕ value (tₘ , ~ᵗ-subst-value t~t vₚ) Eₘ)
  ~ʰ-cons-value {Hₚ} {ρ} {Hₘ} {Eₚ} {Eₘ} {Sₚ} {p} {tₚ} {tₘ} ~ʰ ~ᵗ vₚ ~S =
    subst₂
      (λ ∣S∣ v → Hₚ ∙[ ∣ Sₚ ∣ · p ]ₕ v ~ʰ[ liftRen ρ ] Hₘ ∙[ ∣S∣ · p ]ₕ value (tₘ , ~ᵗ-subst-value ~ᵗ vₚ) Eₘ)
      (~S→∣≡∣ ~S)
      {!   !}
      (~ʰ′-extend ~ʰ)

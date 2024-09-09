open import Graded.Modality

module ArrayLang.Syntax
  {ℓ} {M : Set ℓ}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Tools.Empty
open import Tools.Unit
open import Tools.Bool
open import Tools.Nat using (Nat; 1+) renaming (_+_ to _+Nat_)
open import Tools.Fin using (Fin; x0; _+1)
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Function
open import Tools.Relation
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

open import Data.Product using (Σ-syntax; ∄)
open import Data.Vec

infixr 20 _⊗_
infixr 15 _[_]⇒_

infixl 24 _∙_
infixl 24 _∙[_]_
infix 30 vs_

infix 3 _∋ᶜ_

infixl 20 _•_

infix 10 _⊢_
infix 25 !_
infix 25 let⋆[_]_
infix 25 let![_]_
infix 25 let⊗[_]_
infix 25 let-[_]_
infixl 30 _∘⟨_⟩_
infixl 30 _∘_

data Type : Set ℓ where
  ℕ    : Type
  Unit : Type
  Lin  : Type
  Arr  : Type

  _[_]⇒_ : (A : Type) (p : M) (δ : Type)
         → Type

  _⊗_  : Type → Type → Type
  !_   : Type → Type

private
  variable
    n m k : Nat

-- data ConItem : Type → Set ℓ where
--   var : (A : Type) → ConItem A
--   ref : ConItem Arr

data Con : Nat → Set ℓ where
  ε   : Con 0
  _∙_ : (Γ : Con n) (A : Type)
      → Con (1+ n)

private
  variable
    A B C A′ : Type
    Γ Δ Θ : Con n
    p q r : M

data _∋ᶜ_ : Con n → Type → Set ℓ where
  vz   : Γ ∙ A ∋ᶜ A
  vs_  : Γ ∋ᶜ A
       → Γ ∙ B ∋ᶜ A

toFin : {Γ : Con n} → Γ ∋ᶜ A → Fin n
toFin vz = x0
toFin (vs x) = toFin x +1

data _⊢_ {n} : Con n → Type → Set ℓ where
  `_ : Γ ∋ᶜ A
     → Γ ⊢ A

  lam : (p : M)
      → Γ ∙ A ⊢ B
      → Γ ⊢ A [ p ]⇒ B
  _∘_ : Γ ⊢ A [ p ]⇒ B
      → Γ ⊢ A
      → Γ ⊢ B

  zero : Γ ⊢ ℕ
  suc  : Γ ⊢ ℕ → Γ ⊢ ℕ

  star : Γ ⊢ Unit
  let⋆[_]_ : Γ ⊢ Unit
           → Γ ⊢ B
           → Γ ⊢ B

  !_ : Γ ⊢   A
     → Γ ⊢ ! A
  let![_]_ : Γ ⊢ ! A
           → Γ ∙ A ⊢ B
           → Γ ⊢ B

  ⟨_,_⟩ : Γ ⊢ A
        → Γ ⊢     B
        → Γ ⊢ A ⊗ B
  let⊗[_]_ : Γ ⊢ A ⊗ B
           → Γ ∙ A ∙ B ⊢ C
           → Γ ⊢ C

  linearly  : Γ ∙ Lin ⊢ ! A
            → Γ ⊢ ! A
  consume   : Γ ⊢ Lin
            → Γ ⊢ Unit
  duplicate : Γ ⊢ Lin
            → Γ ⊢ Lin ⊗ Lin

  new   : Γ ⊢ Lin
        → Γ ⊢ ℕ
        → Γ ⊢ Arr

  read  : Γ ⊢ Arr
        → Γ ⊢ ℕ
        → Γ ⊢ Arr ⊗ ! ℕ

  write : Γ ⊢ Arr
        → Γ ⊢ ℕ -- index
        → Γ ⊢ ℕ -- value
        → Γ ⊢ Arr

  free  : Γ ⊢ Arr
        → Γ ⊢ Unit

fromNat : Nat → Γ ⊢ ℕ
fromNat 0 = zero
fromNat (1+ n) = suc (fromNat n)

pattern _∘⟨_⟩_ t p u = _∘_ {p = p} t u

let-[_]_ : {p : M}
         → (t : Γ ⊢ A)
         → (u : Γ ∙ A ⊢ B)
         → Γ ⊢ B
let-[_]_ {p = p} t u = (lam p u) ∘ t

private
  variable
    x y : _ ∋ᶜ _

vz≢vs : vz ≢ vs x
vz≢vs ()

vs-inj : {x : Γ ∋ᶜ A} {y : Γ ∋ᶜ A}
       → vs_ {B = B} x ≡ vs y
       → x ≡ y
vs-inj refl = refl

dec-var : {A B : Type}
        → (x : Γ ∋ᶜ A) (y : Γ ∋ᶜ B)
        → Dec (Σ (A ≡ B) λ A≡B → subst (Γ ∋ᶜ_) A≡B x ≡ y)
dec-var vz     vz     = yes (refl , refl)
dec-var vz     (vs y) = no λ where (refl , vz≡vs) → vz≢vs vz≡vs
dec-var (vs x) vz     = no λ where (refl , vs≡vz) → vz≢vs (sym vs≡vz)
dec-var (vs x) (vs y) = case dec-var x y of λ where
  (yes (refl , refl)) → yes (refl , refl)
  (no x≢y) → no λ where (refl , refl) → x≢y (refl , refl)

-- Renamings

Distinct : Γ ∋ᶜ A → Γ ∋ᶜ B → Set
Distinct vz     vz     = ⊥
Distinct vz     (vs _) = ⊤
Distinct (vs _) vz     = ⊤
Distinct (vs x) (vs y) = Distinct x y

Equal : Γ ∋ᶜ A → Γ ∋ᶜ B → Set
Equal vz     vz     = ⊤
Equal vz     (vs _) = ⊥
Equal (vs _) vz     = ⊥
Equal (vs x) (vs y) = Equal x y

dec-var′ : (x : Γ ∋ᶜ A) (y : Γ ∋ᶜ B)
         → Equal x y ⊎ Distinct x y
dec-var′ vz     vz     = inj₁ tt
dec-var′ vz     (vs y) = inj₂ tt
dec-var′ (vs x) vz     = inj₂ tt
dec-var′ (vs x) (vs y) = dec-var′ x y

dec-Distinct : (x : Γ ∋ᶜ A) (y : Γ ∋ᶜ B) → Dec (Distinct x y)
dec-Distinct vz vz = no idᶠ
dec-Distinct vz (vs y) = yes tt
dec-Distinct (vs x) vz = yes tt
dec-Distinct (vs x) (vs y) = dec-Distinct x y

Distinct-prop : (x : Γ ∋ᶜ A) (y : Γ ∋ᶜ B)
              → (d₁ d₂ : Distinct x y)
              → d₁ ≡ d₂
Distinct-prop vz     (vs _) _  _  = refl
Distinct-prop (vs _) vz     _  _  = refl
Distinct-prop (vs x) (vs y) d₁ d₂ = Distinct-prop x y d₁ d₂

mutual
  data Ren : Con n → Con m → Set ℓ where
    ε   : Ren Γ ε
    _∙_ : (ρ : Ren Γ Δ)
          (x : Γ ∋ᶜ A)
        → ⦃ x∉ρ : x ∉ʳ ρ ⦄
        → Ren Γ (Δ ∙ A)

  pattern _∙[_]_ ρ x∉ρ x = _∙_ ρ x ⦃ x∉ρ ⦄

  _∉ʳ_ : Γ ∋ᶜ A → Ren Γ Δ → Set
  x ∉ʳ ε       = ⊤
  x ∉ʳ (ρ ∙ y) = Distinct x y × x ∉ʳ ρ

instance
  ∉-nil : {x : Γ ∋ᶜ A} → x ∉ʳ ε
  ∉-nil = tt

  ∉-cons : {x : Γ ∋ᶜ A} {y : Γ ∋ᶜ B} {ρ : Ren Γ Δ}
         → ⦃ Distinct x y ⦄
         → ⦃ x∉ρ : x ∉ʳ ρ ⦄
         → ⦃ y∉ρ : y ∉ʳ ρ ⦄
         → x ∉ʳ ρ ∙[ y∉ρ ] y
  ∉-cons ⦃ (x≠y) ⦄ ⦃ x∉ρ ⦄ = x≠y , x∉ρ

∉ʳ-prop : (ρ : Ren Γ Δ) {x : Γ ∋ᶜ A}
          (p₁ p₂ : x ∉ʳ ρ)
        → p₁ ≡ p₂
∉ʳ-prop ε _ _ = refl
∉ʳ-prop (_ ∙ y) {x} (d₁ , p₁) (d₂ , p₂) = cong₂ _,_ (Distinct-prop x y d₁ d₂) (∉ʳ-prop _ _ _)

renVar : Ren Γ Δ → Δ ∋ᶜ A → Γ ∋ᶜ A
renVar (_ ∙ y) vz     = y
renVar (ρ ∙ _) (vs x) = renVar ρ x

mutual
  stepRen : Ren Γ Δ
          → Ren (Γ ∙ A) Δ
  stepRen ε = ε
  stepRen (ρ ∙[ x∉ρ ] x) = stepRen ρ ∙[ step∉ x∉ρ ] vs x

  step∉ : {x : Γ ∋ᶜ A} {ρ : Ren Γ Δ}
        → x ∉ʳ ρ
        → vs_ {B = B} x ∉ʳ stepRen ρ
  step∉ {ρ = ε} _ = tt
  step∉ {ρ = ρ ∙[ x∉ρ ] _} (d , y∉ρ) = d , step∉ y∉ρ

vz∉step : (ρ : Ren Γ Δ)
        → vz {A = A} ∉ʳ stepRen ρ
vz∉step ε = tt
vz∉step (ρ ∙ _) = tt , vz∉step ρ

liftRen : Ren Γ Δ → Ren (Γ ∙ A) (Δ ∙ A)
liftRen ρ = stepRen ρ ∙[ vz∉step _ ] vz

idRen : {Γ : Con n} → Ren Γ Γ
idRen {Γ = ε}     = ε
idRen {Γ = _ ∙ _} = liftRen idRen

ren : Ren Γ Δ → Δ ⊢ A → Γ ⊢ A
ren ρ (` x)           = ` renVar ρ x
ren ρ (lam p t)       = lam p (ren (liftRen ρ) t)
ren ρ (t ∘ t₁)        = ren ρ t ∘ ren ρ t₁
ren ρ zero            = zero
ren ρ (suc t)         = suc (ren ρ t)
ren ρ star            = star
ren ρ (let⋆[ t ] t₁)  = let⋆[ ren ρ t ] ren ρ t₁
ren ρ (! t)           = ! ren ρ t
ren ρ (let![ t ] t₁)  = let![ ren ρ t ] ren (liftRen ρ) t₁
ren ρ ⟨ t , t₁ ⟩      = ⟨ ren ρ t , ren ρ t₁ ⟩
ren ρ (let⊗[ t ] t₁)  = let⊗[ ren ρ t ] ren (liftRen (liftRen ρ)) t₁
ren ρ (linearly t)    = linearly (ren (liftRen ρ) t)
ren ρ (consume t)     = consume (ren ρ t)
ren ρ (duplicate t)   = duplicate (ren ρ t)
ren ρ (new t t₁)      = new (ren ρ t) (ren ρ t₁)
ren ρ (read t t₁)     = read (ren ρ t) (ren ρ t₁)
ren ρ (write t t₁ t₂) = write (ren ρ t) (ren ρ t₁) (ren ρ t₂)
ren ρ (free t)        = free (ren ρ t)

private
  variable
    ρ : Ren _ _
    t t′ u u′ t₁ t₁′ t₂ t₂′ t₃ t₃′ : _ ⊢ _

-- Inversion lemmas for renaming

ren-var : {x : Γ ∋ᶜ A}
          {t : Δ ⊢ A}
          {ρ : Ren Γ Δ}
        → ren ρ t ≡ ` x
        → ∃ λ (x′ : Δ ∋ᶜ A) → t ≡ ` x′ × renVar ρ x′ ≡ x
ren-var {t = ` _} refl = _ , refl , refl

ren-lam : ren ρ t ≡ lam p u
        → ∃ λ u′ → t ≡ lam p u′ × ren (liftRen ρ) u′ ≡ u
ren-lam {t = lam _ _} refl = _ , refl , refl

ren-app : ren ρ t ≡ t₁ ∘ t₂
        → ∃₂ λ t₁′ t₂′ → t ≡ t₁′ ∘ t₂′ × ren ρ t₁′ ≡ t₁ × ren ρ t₂′ ≡ t₂
ren-app {t = _ ∘ _} refl = _ , _ , refl , refl , refl

ren-zero : ren ρ t ≡ zero
         → t ≡ zero
ren-zero {t = zero} refl = refl

ren-suc : ren ρ t ≡ suc t₁
        → ∃ λ t₁′ → t ≡ suc t₁′ × ren ρ t₁′ ≡ t₁
ren-suc {t = suc _} refl = _ , refl , refl

ren-star : ren ρ t ≡ star
         → t ≡ star
ren-star {t = star} refl = refl

ren-let⋆ : ren ρ t ≡ let⋆[ t₁ ] t₂
         → ∃₂ λ t₁′ t₂′ → t ≡ let⋆[ t₁′ ] t₂′ × ren ρ t₁′ ≡ t₁ × ren ρ t₂′ ≡ t₂
ren-let⋆ {t = let⋆[ _ ] _} refl = _ , _ , refl , refl , refl

ren-! : ren ρ t ≡ ! t₁
      → ∃ λ t₁′ → t ≡ ! t₁′ × ren ρ t₁′ ≡ t₁
ren-! {t = ! _} refl = _ , refl , refl

ren-let! : ren ρ t ≡ let![ t₁ ] t₂
         → ∃₂ λ t₁′ t₂′ → t ≡ let![ t₁′ ] t₂′ × ren ρ t₁′ ≡ t₁ × ren (liftRen ρ) t₂′ ≡ t₂
ren-let! {t = let![ _ ] _} refl = _ , _ , refl , refl , refl

ren-⟨,⟩ : ren ρ t ≡ ⟨ t₁ , t₂ ⟩
       → ∃₂ λ t₁′ t₂′ → t ≡ ⟨ t₁′ , t₂′ ⟩ × ren ρ t₁′ ≡ t₁ × ren ρ t₂′ ≡ t₂
ren-⟨,⟩ {t = ⟨ _ , _ ⟩} refl = _ , _ , refl , refl , refl

ren-let⊗ : ren ρ t ≡ let⊗[ t₁ ] t₂
         → ∃₂ λ t₁′ t₂′ → t ≡ let⊗[ t₁′ ] t₂′ × ren ρ t₁′ ≡ t₁ × ren (liftRen (liftRen ρ)) t₂′ ≡ t₂
ren-let⊗ {t = let⊗[ _ ] _} refl = _ , _ , refl , refl , refl

ren-linearly : ren ρ t ≡ linearly t₁
             → ∃ λ t₁′ → t ≡ linearly t₁′ × ren (liftRen ρ) t₁′ ≡ t₁
ren-linearly {t = linearly _} refl = _ , refl , refl

ren-consume : ren ρ t ≡ consume t₁
            → ∃ λ t₁′ → t ≡ consume t₁′ × ren ρ t₁′ ≡ t₁
ren-consume {t = consume _} refl = _ , refl , refl

ren-duplicate : ren ρ t ≡ duplicate t₁
              → ∃ λ t₁′ → t ≡ duplicate t₁′ × ren ρ t₁′ ≡ t₁
ren-duplicate {t = duplicate _} refl = _ , refl , refl

ren-new : ren ρ t ≡ new t₁ t₂
        → ∃₂ λ t₁′ t₂′ → t ≡ new t₁′ t₂′ × ren ρ t₁′ ≡ t₁ × ren ρ t₂′ ≡ t₂
ren-new {t = new _ _} refl = _ , _ , refl , refl , refl

ren-read : ren ρ t ≡ read t₁ t₂
         → ∃₂ λ t₁′ t₂′ → t ≡ read t₁′ t₂′ × ren ρ t₁′ ≡ t₁ × ren ρ t₂′ ≡ t₂
ren-read {t = read _ _} refl = _ , _ , refl , refl , refl

ren-write : ren ρ t ≡ write t₁ t₂ t₃
          → ∃₃ λ t₁′ t₂′ t₃′ → t ≡ write t₁′ t₂′ t₃′ × ren ρ t₁′ ≡ t₁ × ren ρ t₂′ ≡ t₂ × ren ρ t₃′ ≡ t₃
ren-write {t = write _ _ _} refl = _ , _ , _ , refl , refl , refl , refl

ren-free : ren ρ t ≡ free t₁
         → ∃ λ t₁′ → t ≡ free t₁′ × ren ρ t₁′ ≡ t₁
ren-free {t = free _} refl = _ , refl , refl

ren1 : (B : Type) → Γ ⊢ A → Γ ∙ B ⊢ A
ren1 _ = ren (stepRen idRen)

`-inj : {x y : Γ ∋ᶜ A}
      → ` x ≡ ` y
      → x ≡ y
`-inj refl = refl

∘-inj : {t₁  : Γ ⊢ A  [ p ]⇒ B} {t₂  : Γ ⊢ A}
      → {t₁′ : Γ ⊢ A′ [ p ]⇒ B} {t₂′ : Γ ⊢ A′}
      → t₁ ∘ t₂ ≡ t₁′ ∘ t₂′
      → Σ (A ≡ A′) λ A≡A′
                   → subst (λ A → Γ ⊢ A [ p ]⇒ B) A≡A′ t₁ ≡ t₁′
                   × subst (Γ ⊢_) A≡A′ t₂ ≡ t₂′
∘-inj refl = _ , refl , refl

Distinct→≢ : {A B : Type}
           → (x : Γ ∋ᶜ A) (y : Γ ∋ᶜ B)
           → Distinct x y
           → ¬ Σ (A ≡ B) λ A≡B → subst (Γ ∋ᶜ_) A≡B x ≡ y
Distinct→≢ vz     vz     ⊥ = ⊥-elim ⊥
Distinct→≢ vz     (vs _) tt = λ where
  (refl , vz≡vs) → vz≢vs vz≡vs
Distinct→≢ (vs _) vz     tt = λ where
  (refl , vs≡vz) → vz≢vs (sym vs≡vz)
Distinct→≢ (vs x) (vs y) distinct = λ where
  (refl , vs-x≡vs-y) → Distinct→≢ x y distinct (refl , vs-inj vs-x≡vs-y)

≢→Distinct : {A B : Type}
           → (x : Γ ∋ᶜ A) (y : Γ ∋ᶜ B)
           → ¬ (Σ (A ≡ B) λ A≡B → subst (Γ ∋ᶜ_) A≡B x ≡ y)
           → Distinct x y
≢→Distinct vz vz ≢ = ≢ (refl , refl)
≢→Distinct vz (vs _) _ = tt
≢→Distinct (vs _) vz _ = tt
≢→Distinct (vs x) (vs y) ≢ = ≢→Distinct x y λ where
  (refl , x≡y) → ≢ (refl , cong vs_ x≡y)

≢→Distinct′ : (x y : Γ ∋ᶜ A)
            → x ≢ y
            → Distinct x y
≢→Distinct′ x y ≢ = ≢→Distinct x y λ where (refl , refl) → ≢ refl

Distinct→≢′ : (x y : Γ ∋ᶜ A)
            → Distinct x y
            → x ≢ y
Distinct→≢′ x y distinct x≡y = Distinct→≢ x y distinct (refl , x≡y)

¬Distinct-refl : (x : Γ ∋ᶜ A) → ¬ (Distinct x x)
¬Distinct-refl x distinct = Distinct→≢′ x x distinct refl

Distinct-sym : (x : Γ ∋ᶜ A) (y : Γ ∋ᶜ B) → Distinct x y → Distinct y x
Distinct-sym (vz)   (vs y) _ = tt
Distinct-sym (vs x) (vz)   _ = tt
Distinct-sym (vs x) (vs y) ≠ = Distinct-sym x y ≠

Distinct-renVar
  : (ρ : Ren Γ Δ) {x : Δ ∋ᶜ A} {y : Γ ∋ᶜ B}
  → y ∉ʳ ρ
  → Distinct (renVar ρ x) y
Distinct-renVar (ρ ∙ z) {x = vz}   {y} (d , _)   = Distinct-sym y z d
Distinct-renVar (ρ ∙ _) {x = vs _}     (_ , y∉ρ) = Distinct-renVar ρ y∉ρ

renVar≠ : (ρ : Ren Γ Δ) {x : Δ ∋ᶜ A} {y : Δ ∋ᶜ B}
        → Distinct x y
        → Distinct (renVar ρ x) (renVar ρ y)
renVar≠ (ρ ∙[ x∉ρ ] z) {x = vs x} {y = vz}   _   = Distinct-renVar ρ x∉ρ
renVar≠ (ρ ∙[ x∉ρ ] z) {x = vz}   {y = vs y} _   = Distinct-sym _ z (Distinct-renVar ρ x∉ρ)
renVar≠ (ρ ∙        _) {x = vs x} {y = vs y} x≠y = renVar≠ ρ x≠y


renVar∉ : (ρ : Ren Γ Δ)
        → (x : Γ ∋ᶜ A)
        → x ∉ʳ ρ
        → (y : Δ ∋ᶜ B)
        → Distinct x (renVar ρ y)
renVar∉ (ρ ∙ z) x (x≢z , _)  vz     = x≢z
renVar∉ (ρ ∙ _) x (_ , ρy∉ρ) (vs y) = renVar∉ ρ x ρy∉ρ y

renVar-step : (ρ : Ren Γ Δ) (x : Δ ∋ᶜ A)
            → renVar (stepRen {A = B} ρ) x ≡ vs (renVar ρ x)
renVar-step (ρ ∙ _) vz     = refl
renVar-step (ρ ∙ _) (vs x) = renVar-step ρ x

renVar-id : {Γ : Con n} {x : Γ ∋ᶜ A} → renVar (idRen {Γ = Γ}) x ≡ x
renVar-id {Γ = Γ ∙ _} {x = vz}   = refl
renVar-id {Γ = Γ ∙ _} {x = vs x} = trans (renVar-step idRen x) (cong vs_ renVar-id)

renVar-unstep : (ρ : Ren Γ Δ)
              → (x : Δ ∋ᶜ A) (y : Γ ∋ᶜ A)
              → renVar (stepRen {A = B} ρ) x ≡ vs y
              → renVar ρ x ≡ y
renVar-unstep ρ x y renVar≡vs = vs-inj (begin
  vs (renVar ρ x)      ≡˘⟨ renVar-step ρ x ⟩
  renVar (stepRen ρ) x ≡⟨ renVar≡vs ⟩
  vs y ∎)

renVar-lift-vs : (ρ : Ren Γ Δ) (x : Δ ∋ᶜ A)
               → renVar (liftRen {A = B} ρ) (vs x) ≡ vs (renVar ρ x)
renVar-lift-vs (ρ ∙ _) vz     = refl
renVar-lift-vs (ρ ∙ _) (vs x) = renVar-step ρ x

renVar-unlift-vz : (ρ : Ren Γ Δ) (x : Δ ∙ A ∋ᶜ A)
                 → renVar (liftRen ρ) x ≡ vz
                 → x ≡ vz
renVar-unlift-vz _ vz     _         = refl
renVar-unlift-vz ρ (vs x) renVar≡vz = ⊥-elim (vz≢vs (begin
  vz                   ≡˘⟨ renVar≡vz ⟩
  renVar (stepRen ρ) x ≡⟨ renVar-step ρ x ⟩
  vs renVar ρ x        ∎))

renVar-unlift-vs : (ρ : Ren Γ Δ)
                 → (x : Δ ∙ B ∋ᶜ A) (y : Γ ∋ᶜ A)
                 → renVar (liftRen ρ) x ≡ vs y
                 → ∃ λ x′ → x ≡ vs x′ × renVar ρ x′ ≡ y
renVar-unlift-vs ρ (vs x) y [step-ρ]x≡vs-y = x , refl , renVar-unstep ρ x y [step-ρ]x≡vs-y

mutual
  remapRen : Δ ∋ᶜ A
           → Ren Γ Δ
           → Ren (Γ ∙ A) Δ
  remapRen vz     (ρ ∙ _)        = liftRen ρ
  remapRen (vs x) (ρ ∙[ y∉ρ ] y) = remapRen x ρ ∙[ vs∉remap y∉ρ ] vs y

  vs∉remap : {ρ : Ren Γ Δ}
           → {x : Γ ∋ᶜ A} (x∉ρ : x ∉ʳ ρ)
           → {y : Δ ∋ᶜ B}
           → (vs x) ∉ʳ remapRen y ρ
  vs∉remap {ρ = _ ∙ _} (x≠y , x∉ρ) {y = vz}   = tt , (step∉ x∉ρ)
  vs∉remap {ρ = _ ∙ _} (x≠y , x∉ρ) {y = vs y} = x≠y , vs∉remap x∉ρ

renVar-remap-vz : (ρ : Ren Γ Δ)
                → (x : Δ ∋ᶜ A)
                → renVar (remapRen x ρ) x ≡ vz
renVar-remap-vz (ρ ∙ _) vz     = refl
renVar-remap-vz (ρ ∙ _) (vs x) = renVar-remap-vz ρ x

renVar-remap-vs : {A B : Type}
                → (ρ : Ren Γ Δ)
                → (x : Δ ∋ᶜ A) (y : Δ ∋ᶜ B) (z : Γ ∋ᶜ A)
                → renVar ρ x ≡ z
                → Distinct x y
                → renVar (remapRen y ρ) x ≡ vs z
renVar-remap-vs (_ ∙ _) vz     (vs _) _ refl _   = refl
renVar-remap-vs (ρ ∙ _) (vs x) vz     _ refl _   = renVar-step ρ x
renVar-remap-vs (ρ ∙ _) (vs x) (vs y) z ρx≡z x≢y = renVar-remap-vs ρ x y z ρx≡z x≢y

renVar-unremap-vz : (ρ : Ren Γ Δ)
                  → (x : Δ ∋ᶜ A) (y : Δ ∋ᶜ A)
                  → renVar (remapRen y ρ) x ≡ vz
                  → x ≡ y
renVar-unremap-vz (ρ ∙ _) x      vz     [lift-ρ]x≡vz    = renVar-unlift-vz ρ x [lift-ρ]x≡vz
renVar-unremap-vz (ρ ∙ _) (vs x) (vs y) [remap-ρ-y]x≡vz = cong vs_ (renVar-unremap-vz ρ x y [remap-ρ-y]x≡vz)

renVar-unremap-vs : (ρ : Ren Γ Δ)
           → (x : Δ ∋ᶜ A) (y : Δ ∋ᶜ B) (z : Γ ∋ᶜ A)
           → renVar (remapRen y ρ) x ≡ vs z
           → renVar ρ x ≡ z
renVar-unremap-vs (ρ ∙ _) x vz     z [lift-ρ]x≡vs-z =
  case renVar-unlift-vs ρ x z [lift-ρ]x≡vs-z of λ where (x′ , refl , ρx′≡z) → ρx′≡z
renVar-unremap-vs (ρ ∙ _) vz (vs y) z vs-x≡vs-z = vs-inj vs-x≡vs-z
renVar-unremap-vs (ρ ∙ _) (vs x) (vs y) z [remap-ρ-y]x≡vs-z = renVar-unremap-vs ρ x y z [remap-ρ-y]x≡vs-z

renVar-unremap-≢ : (ρ : Ren Γ Δ)
                 → (x : Δ ∋ᶜ A) (y : Δ ∋ᶜ B) (z : Γ ∙ B ∋ᶜ A)
                 → renVar (remapRen y ρ) x ≡ z
                 → Distinct z (vs renVar ρ y)
renVar-unremap-≢ (ρ ∙ w) x vz vz _ =  tt
renVar-unremap-≢ (ρ ∙[ w∉ρ ] w) x vz (vs z) [lift-ρ]x≡z =
  case renVar-unlift-vs ρ x z [lift-ρ]x≡z of λ where
    (x′ , refl , refl) → Distinct-sym w _ (renVar∉ ρ w w∉ρ x′)
renVar-unremap-≢ (ρ ∙[ w∉ρ ] w) vz (vs y) (vs z) vs-w≡vs-z =
  case vs-inj vs-w≡vs-z of λ where refl → renVar∉ ρ w w∉ρ y
renVar-unremap-≢ (ρ ∙ _) (vs x) (vs y) z [remap-y-ρ]x≡z = renVar-unremap-≢ ρ x y z [remap-y-ρ]x≡z

renVar-inj : (ρ : Ren Γ Δ)
           → (x y : Δ ∋ᶜ A)
           → renVar ρ x ≡ renVar ρ y
           → x ≡ y
renVar-inj (ρ ∙ _)         vz     vz     _     = refl
renVar-inj (ρ ∙[ ρy∉ρ ] _) vz     (vs y) refl  = ⊥-elim (¬Distinct-refl (renVar ρ y) (renVar∉ ρ _ ρy∉ρ y))
renVar-inj (ρ ∙[ ρx∉ρ ] _) (vs x) vz     refl  = ⊥-elim (¬Distinct-refl (renVar ρ x) (renVar∉ ρ _ ρx∉ρ x))
renVar-inj (ρ ∙ _)         (vs x) (vs y) ρx≡ρy = cong vs_ (renVar-inj ρ x y ρx≡ρy)

mutual
  _•_ : Ren Γ Δ
      → Ren Δ Θ
      → Ren Γ Θ
  ρ • ε              = ε
  ρ • (σ ∙[ x∉σ ] x) = (ρ • σ) ∙[ renVar∉• x∉σ ] renVar ρ x

  renVar∉• : {ρ : Ren Γ Δ} {σ : Ren Δ Θ}
           → {x : Δ ∋ᶜ A}
           → x ∉ʳ σ
           → renVar ρ x ∉ʳ (ρ • σ)
  renVar∉•         {σ = ε}     _           = tt
  renVar∉• {ρ = ρ} {σ = σ ∙ y} (x≠y , x∉σ) = renVar≠ ρ x≠y , renVar∉• x∉σ

•-cong : {ρ₁ ρ₂ : Ren Γ Δ} {x₁ x₂ : Γ ∋ᶜ A} {x₁∉ρ₁ : x₁ ∉ʳ ρ₁} {x₂∉ρ₂ : x₂ ∉ʳ ρ₂}
       → (ρ₁≡ρ₂ : ρ₁ ≡ ρ₂)
       → (x₁≡x₂ : x₁ ≡ x₂)
       → ρ₁ ∙[ x₁∉ρ₁ ] x₁ ≡ ρ₂ ∙[ x₂∉ρ₂ ] x₂
•-cong ρ₁≡ρ₂ x₁≡x₂ = •-cong′ ρ₁≡ρ₂ x₁≡x₂ (∉ʳ-prop _ _ _)
  where
    •-cong′ : {ρ₁ ρ₂ : Ren Γ Δ} {x₁ x₂ : Γ ∋ᶜ A} {x₁∉ρ₁ : x₁ ∉ʳ ρ₁} {x₂∉ρ₂ : x₂ ∉ʳ ρ₂}
            → (ρ₁≡ρ₂ : ρ₁ ≡ ρ₂)
            → (x₁≡x₂ : x₁ ≡ x₂)
            → subst₂ _∉ʳ_ x₁≡x₂ ρ₁≡ρ₂ x₁∉ρ₁ ≡ x₂∉ρ₂
            → ρ₁ ∙[ x₁∉ρ₁ ] x₁ ≡ ρ₂ ∙[ x₂∉ρ₂ ] x₂
    •-cong′ refl refl refl = refl

•-step : (ρ : Ren Γ Δ) (σ : Ren Δ Θ)
       → {x∉ρ : x ∉ʳ ρ}
       → (ρ ∙[ x∉ρ ] x) • stepRen σ ≡ ρ • σ
•-step ρ ε = refl
•-step ρ (σ ∙ x) = •-cong (•-step ρ σ) refl

•-identityˡ : (ρ : Ren Γ Δ)
            → idRen • ρ ≡ ρ
•-identityˡ ε = refl
•-identityˡ (ρ ∙[ x∉ρ ] x) = •-cong (•-identityˡ ρ) renVar-id

•-identityʳ : {Γ : Con n} {Δ : Con m}
            → (ρ : Ren Γ Δ)
            → ρ • idRen ≡ ρ
•-identityʳ ε       = refl
•-identityʳ (ρ ∙ x) = •-cong (trans (•-step ρ idRen) (•-identityʳ ρ)) refl

∙-inj : (ρ σ : Ren Γ Δ)
      → (x y : Γ ∋ᶜ A)
      → {x∉ρ : x ∉ʳ ρ} {y∉σ : y ∉ʳ σ}
      → ρ ∙[ x∉ρ ] x ≡ σ ∙[ y∉σ ] y
      → ρ ≡ σ × x ≡ y
∙-inj ρ .ρ x .x refl = refl , refl

•-injʳ : (ρ : Ren Γ Δ) (σ σ′ : Ren Δ Θ)
       → ρ • σ ≡ ρ • σ′
       → σ ≡ σ′
•-injʳ _ ε ε _ = refl
•-injʳ ρ (σ ∙[ x∉σ ] x) (σ′ ∙[ y∉σ′ ] y) eq =
  case ∙-inj (ρ • σ) (ρ • σ′) _ _ eq of λ { (ρ•σ≡ρ•σ′ , ρx≡ρy) →
  case •-injʳ ρ σ σ′ ρ•σ≡ρ•σ′ of λ { refl →
  case renVar-inj ρ x y ρx≡ρy of λ { refl →
  case ∉ʳ-prop σ x∉σ y∉σ′ of λ { refl →
  refl
  }
  }
  }
  }

renVar-comp : (ρ : Ren Γ Δ) (σ : Ren Δ Θ) (x : Θ ∋ᶜ A)
            → renVar ρ (renVar σ x) ≡ renVar (ρ • σ) x
renVar-comp _ (_ ∙ _) vz     = refl
renVar-comp ρ (σ ∙ _) (vs x) = renVar-comp ρ σ x

stepRen-comp : (ρ : Ren Γ Δ) (σ : Ren Δ Θ)
             → stepRen {A = A} ρ • σ ≡ stepRen (ρ • σ)
stepRen-comp ρ ε              = refl
stepRen-comp ρ (σ ∙[ x∉σ ] x) = cong₂ (λ σ y → σ ∙[ {!!} ] y) (stepRen-comp ρ σ) (renVar-step ρ x)

liftRen-comp : (ρ : Ren Γ Δ) (σ : Ren Δ Θ)
             → liftRen {A = A} ρ • liftRen σ ≡ liftRen (ρ • σ)
liftRen-comp ρ ε                           = refl
liftRen-comp (ρ ∙[ x∉ρ ] x) (σ ∙[ y∉σ ] y) = cong₂ (λ η z → η ∙[ {!!} ] z ∙[ {!!} ] vz) {!!} {!renVar-step !}

ren-comp : (ρ : Ren Γ Δ) (σ : Ren Δ Θ) (t : Θ ⊢ A)
         → ren ρ (ren σ t) ≡ ren (ρ • σ) t
ren-comp ρ σ (` x)           = cong `_ (renVar-comp ρ σ x)
ren-comp ρ σ (lam p t)       = cong (lam p) {!ren-comp (liftRen ρ) (liftRen σ) t!}
ren-comp ρ σ (t ∘ t₁)        = cong₂ _∘_ (ren-comp ρ σ t) (ren-comp ρ σ t₁)
ren-comp ρ σ zero            = refl
ren-comp ρ σ (suc t)         = cong suc (ren-comp ρ σ t)
ren-comp ρ σ star            = refl
ren-comp ρ σ (let⋆[ t ] t₁)  = cong₂ let⋆[_]_ (ren-comp ρ σ t) (ren-comp ρ σ t₁)
ren-comp ρ σ (! t)           = cong !_ (ren-comp ρ σ t)
ren-comp ρ σ (let![ t ] t₁)  = cong₂ let![_]_ (ren-comp ρ σ t) {!ren-comp (liftRen ρ) (liftRen σ) t₁!}
ren-comp ρ σ ⟨ t , t₁ ⟩      = cong₂ ⟨_,_⟩ (ren-comp ρ σ t) (ren-comp ρ σ t₁)
ren-comp ρ σ (let⊗[ t ] t₁)  = cong₂ let⊗[_]_ (ren-comp ρ σ t) {!ren-comp (liftRen ρ) (liftRen σ) t₁!}
ren-comp ρ σ (linearly t)    = cong linearly
  (subst (λ η → ren (liftRen ρ) (ren (liftRen σ) t) ≡ ren η t)
         (liftRen-comp _ _)
         (ren-comp (liftRen ρ) (liftRen σ) t))
ren-comp ρ σ (consume t)     = cong consume (ren-comp ρ σ t)
ren-comp ρ σ (duplicate t)   = cong duplicate (ren-comp ρ σ t)
ren-comp ρ σ (new t t₁)      = cong₂ new (ren-comp ρ σ t) (ren-comp ρ σ t₁)
ren-comp ρ σ (read t t₁)     = cong₂ read (ren-comp ρ σ t) (ren-comp ρ σ t₁)
ren-comp ρ σ (write t t₁ t₂) = cong₃ write (ren-comp ρ σ t) (ren-comp ρ σ t₁) (ren-comp ρ σ t₂)
ren-comp ρ σ (free t)        = cong free (ren-comp ρ σ t)

•-assoc : ∀ {n₁ n₂ n₃ n₄}
          {Γ : Con n₁} {Δ : Con n₂} {Θ : Con n₃} {Λ : Con n₄} →
          (ρ : Ren Γ Δ) (σ : Ren Δ Θ) (η : Ren Θ Λ) →
          ρ • (σ • η) ≡ ρ • σ • η
•-assoc _ _ ε = refl
•-assoc ρ σ (η ∙ x) = •-cong (•-assoc ρ σ η) (renVar-comp ρ σ x)

module _ where
  open import Graded.Context 𝕄
  open import Tools.PropositionalEquality

  renConₘ : {Γ : Con m} {Δ : Con n}
          → Ren Γ Δ
          → Conₘ n
          → Conₘ m
  renConₘ ε ε = 𝟘ᶜ
  renConₘ (ρ ∙ x) (γ ∙ p) = renConₘ ρ γ , toFin x ≔ p

  private
    variable
      γ : Conₘ n

  open import Graded.Context.Properties 𝕄

  unrelated-update : {Γ : Con n}
                   → (γ : Conₘ n)
                   → (x : Γ ∋ᶜ A) (y : Γ ∋ᶜ B)
                   → Distinct x y
                   → (γ , toFin y ≔ p) ⟨ toFin x ⟩ ≡ γ ⟨ toFin x ⟩
  unrelated-update (_ ∙ _) vz     (vs _) _   = refl
  unrelated-update (_ ∙ _) (vs _) vz     _   = refl
  unrelated-update (γ ∙ _) (vs x) (vs y) x≠y = unrelated-update γ x y x≠y

  ∉→Distinct-renVar : (x : Δ ∋ᶜ A) (y : Γ ∋ᶜ B)
                    → {ρ : Ren Γ Δ}
                    → y ∉ʳ ρ
                    → Distinct (renVar ρ x) y
  ∉→Distinct-renVar (vz)   y {ρ ∙ x} (y≠x , _) = Distinct-sym y x y≠x
  ∉→Distinct-renVar (vs x) y {ρ ∙ _} (_ , y∉ρ) = ∉→Distinct-renVar x y y∉ρ

  -- Renaming of context lookups
  ren-⟨⟩ : (x : Δ ∋ᶜ A) (ρ : Ren Γ Δ)
         → renConₘ ρ γ ⟨ toFin (renVar ρ x) ⟩ ≡ γ ⟨ toFin x ⟩
  ren-⟨⟩ {γ = γ ∙ _} vz     (ρ ∙ y)        = update-lookup (renConₘ ρ γ) (toFin y)
  ren-⟨⟩ {γ = γ ∙ p} (vs x) (ρ ∙[ y∉ρ ] y) = begin
    (renConₘ ρ γ , toFin y ≔ p) ⟨ toFin (renVar ρ x) ⟩ ≡⟨ unrelated-update (renConₘ ρ γ) (renVar ρ x) y
                                                                           (∉→Distinct-renVar x y y∉ρ) ⟩
    renConₘ ρ γ                 ⟨ toFin (renVar ρ x) ⟩ ≡⟨ ren-⟨⟩ x ρ ⟩
    γ                           ⟨ toFin x ⟩            ∎

-- module TermExamples where
--   id⊸ : ε ⊢ Nat [ 𝟙 ]⇒ Nat
--   id⊸ = ƛ var 0

--   id→ : ε ⊢ Nat [ ω ]⇒ Nat
--   id→ = ƛ `[ ω ] 0

--   unit-β : ε ∙ A ⊢ A
--   unit-β = let⋆[ star ] `[ 𝟙 ] 0

--   unit-η : ε ∙ Unit ⊢ Unit
--   unit-η = let⋆[ `[ 𝟙 ] 0 ] star

--   !-β : ε ∙ A ⊢ A
--   !-β = let![ ! `[ ω ] 0 ] `[ ω ] 0

--   !-η : ε ∙ ! A ⊢ ! A
--   !-η = let![ `[ 𝟙 ] 0 ] ! `[ ω ] 0

--   linearly′ : ε ⊢ (Lin ⊸ ! Nat) ⊸ ! Nat
--   linearly′ = ƛ linearly (`[ 𝟙 ] 0)

--   consume′ : ε ⊢ Lin ⊸ Unit
--   consume′ = ƛ consume (`[ 𝟙 ] 0)

--   duplicate′ : ε ⊢ Lin ⊸ Lin ⊗ Lin
--   duplicate′ = ƛ duplicate (`[ 𝟙 ] 0)

--   linearly-consume : ε ⊢ Unit
--   linearly-consume = let![ linearly (ƛ !u) ] (`[ ω ] 0)
--     where
--       !u : ε ∙ Lin ⊢ ! Unit
--       !u = let⋆[ consume (`[ 𝟙 ] 0) ] ! star

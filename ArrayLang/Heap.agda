{-# OPTIONS --with-K #-}
open import Graded.Modality

module ArrayLang.Heap
  {ℓ} {M : Set ℓ}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Agda.Primitive

open import Graded.Context 𝕄
open import Graded.Modality.Properties.Subtraction semiring-with-meet

open import ArrayLang.Syntax 𝕄
open import ArrayLang.Usage 𝕄

open import Tools.Nat
open import Tools.Fin
open import Tools.Product
open import Tools.Function
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

open import Function.Base using (_∋_)
open import Data.Product using (Σ-syntax)
open import Data.Vec using (Vec)

private
  variable
    n m : Nat
    Γ Γ′ Δ Δ′ Θ Θ′ : Con n
    A B C D : Type
    𝓐 𝓑 𝓒 𝓓 : ConItem _
    t u t₁ t₂ : _ ⊢ _
    p p′ q r : M
    ρ : Ren Γ Δ

------------------------------------------------------------------------
-- Values

infix 10 _⊢ᵥ_
data Value {Γ : Con n} : {A : Type} → Γ ⊢ A → Set ℓ where
  lam   : (p : M) → (t : Γ ∙ var A ⊢ B)
        → Value (lam p t)

  zero  : Value zero
  suc   : Value t
        → Value (suc t)

  star  : Value star

  !_    : Value t
        → Value (! t)

  ⟨_,_⟩ : Value t₁ → Value t₂
        → Value (⟨ t₁ , t₂ ⟩)

  ref   : (x : Γ ∋ᶜ ref)
        → Value (` x)

renValue : {Γ : Con n} {Δ : Con m}
        → {t : Γ ⊢ A}
        → (ρ : Ren Δ Γ)
        → Value t
        → Value (ren ρ t)
renValue ρ (lam p t)  = lam p (ren (liftRen _) t)
renValue ρ zero       = zero
renValue ρ (suc v)    = suc (renValue ρ v)
renValue ρ star       = star
renValue ρ (! v)      = ! renValue ρ v
renValue ρ ⟨ v , v₁ ⟩ = ⟨ renValue ρ v , renValue ρ v₁ ⟩
renValue ρ (ref x)    = ref (renVar ρ x)

unrenValue : {Γ : Con n} {Δ : Con m}
          → (ρ : Ren Δ Γ)
          → {t : Γ ⊢ A}
          → Value (ren ρ t)
          → Value t
unrenValue ρ {t = lam p t}   (lam p v)   = lam p t
unrenValue ρ {t = zero}      zero        = zero
unrenValue ρ {t = suc _}     (suc v)     = suc (unrenValue ρ v)
unrenValue ρ {t = star}      star        = star
unrenValue ρ {t = ! _}       (! v)       = ! unrenValue ρ v
unrenValue ρ {t = ⟨ _ , _ ⟩} ⟨ v₁ , v₂ ⟩ = ⟨ unrenValue ρ v₁ , unrenValue ρ v₂ ⟩
unrenValue ρ {t = ` x}       (ref _)     = ref x

_⊢ᵥ_ : Con n → Type → Set ℓ
Γ ⊢ᵥ A = Σ[ t ∈ Γ ⊢ A ] Value t

⦅_⦆ᵛ : Γ ⊢ᵥ A → Γ ⊢ A
⦅ t , _ ⦆ᵛ = t

renᵛ : Ren Δ Γ → Γ ⊢ᵥ A → Δ ⊢ᵥ A
renᵛ ρ (v , value-v) = ren ρ v , renValue ρ value-v

Nat→⊢ᵥ : Nat → Γ ⊢ᵥ ℕ
Nat→⊢ᵥ 0      = zero , zero
Nat→⊢ᵥ (1+ n) = case Nat→⊢ᵥ n of λ { (t , v) → suc t , suc v }

Nat→⊢ : Nat → Γ ⊢ ℕ
Nat→⊢ 0      = zero
Nat→⊢ (1+ n) = suc (Nat→⊢ n)

prop-Value : (v v′ : Value t) → v ≡ v′
prop-Value (lam p t) (lam .p .t) = refl
prop-Value zero zero = refl
prop-Value (suc v) (suc v′) = cong suc (prop-Value v v′)
prop-Value star star = refl
prop-Value (! v) (! v′) = cong !_ (prop-Value v v′)
prop-Value ⟨ v , v₁ ⟩ ⟨ v′ , v₁′ ⟩ = cong₂ ⟨_,_⟩ (prop-Value v v′) (prop-Value v₁ v₁′)
prop-Value (ref x) (ref .x) = refl

------------------------------------------------------------------------
-- Eliminators

data Elim (Γ : Con n) : (A B : Type) → Set ℓ where
  -∘ₑ_   :                   Δ ⊢ A → Ren Γ Δ → Elim Γ (A [ p ]⇒ B)   B
  _∘ₑ-   : Δ ⊢ᵥ A [ p ]⇒ B         → Ren Γ Δ → Elim Γ              A B

  sucₑ   : Elim Γ ℕ ℕ
  !-ₑ    : Elim Γ A (! A)
  ⟨-,_⟩ₑ :          Δ ⊢ B → Ren Γ Δ → Elim Γ A (A ⊗ B)
  ⟨_,-⟩ₑ : Δ ⊢ᵥ A →         Ren Γ Δ → Elim Γ B (A ⊗ B)

  let⋆[-]ₑ   : Δ ⊢ A                 → Ren Γ Δ → Elim Γ Unit A
  let![-]ₑ   : Δ ∙ var A ⊢ B         → Ren Γ Δ → Elim Γ (! A) B
  let⊗[-]ₑ   : Δ ∙ var A ∙ var B ⊢ C → Ren Γ Δ → Elim Γ (A ⊗ B) C

  linearlyₑ  : Γ ∋ᶜ var Lin → Elim Γ (! A) (! A)

  consumeₑ   : Elim Γ Lin Unit
  duplicateₑ : Elim Γ Lin (Lin ⊗ Lin)

  new₁ₑ   : Δ ⊢ Lin       → Ren Γ Δ → Elim Γ     ℕ Arr
  new₂ₑ   :           Nat           → Elim Γ Lin   Arr

  read₁ₑ  : Δ ⊢ Arr       → Ren Γ Δ → Elim Γ     ℕ (Arr ⊗ ! ℕ)
  read₂ₑ  :           Nat           → Elim Γ Arr   (Arr ⊗ ! ℕ)

  write₁ₑ : Δ ⊢ Arr → Δ ⊢ ℕ       → Ren Γ Δ → Elim Γ       ℕ Arr
  write₂ₑ : Δ ⊢ Arr         → Nat → Ren Γ Δ → Elim Γ     ℕ   Arr
  write₃ₑ :           Nat   → Nat           → Elim Γ Arr     Arr

  freeₑ   : Elim Γ Arr Unit

pattern -∘⟨_⟩ₑ_ p u E = -∘ₑ_ {p = p} u E
pattern _∘⟨_⟩ₑ- t p E = _∘ₑ- {p = p} t E

-- Renaming of eliminators

renᵉ : Ren Γ′ Γ → Elim Γ A B → Elim Γ′ A B
renᵉ ρ ((-∘⟨ p ⟩ₑ u) E)  = (-∘⟨ p ⟩ₑ u) (ρ • E)
renᵉ ρ ((t ∘⟨ p ⟩ₑ-) E)  = (t ∘⟨ p ⟩ₑ-) (ρ • E)
renᵉ ρ sucₑ              = sucₑ
renᵉ ρ !-ₑ               = !-ₑ
renᵉ ρ (⟨-, t ⟩ₑ E)      = ⟨-, t ⟩ₑ (ρ • E)
renᵉ ρ (⟨ v ,-⟩ₑ E)      = ⟨ v ,-⟩ₑ (ρ • E)
renᵉ ρ (let⋆[-]ₑ t E)    = let⋆[-]ₑ t (ρ • E)
renᵉ ρ (let![-]ₑ t E)    = let![-]ₑ t (ρ • E)
renᵉ ρ (let⊗[-]ₑ t E)    = let⊗[-]ₑ t (ρ • E)
renᵉ ρ (linearlyₑ x)     = linearlyₑ (renVar ρ x)
renᵉ ρ (consumeₑ)        = consumeₑ
renᵉ ρ (duplicateₑ)      = duplicateₑ
renᵉ ρ (new₁ₑ l E)       = new₁ₑ l (ρ • E)
renᵉ ρ (new₂ₑ s)         = new₂ₑ s
renᵉ ρ (read₁ₑ t E)      = read₁ₑ t (ρ • E)
renᵉ ρ (read₂ₑ n)        = read₂ₑ n
renᵉ ρ (write₁ₑ i v E)   = write₁ₑ i v (ρ • E)
renᵉ ρ (write₂ₑ arr v E) = write₂ₑ arr v (ρ • E)
renᵉ ρ (write₃ₑ arr i)   = write₃ₑ arr i
renᵉ ρ freeₑ             = freeₑ

ren1ᵉ : (𝓐 : ConItem C) → Elim Γ A B → Elim (Γ ∙ 𝓐) A B
ren1ᵉ _ = renᵉ (stepRen idRen)

-- Evaluation stacks, indexed by the size of the heap

data Stack (Γ : Con n) : Type → Type → Set ℓ where
  ε : Stack Γ A A
  _∙_ : (e : Elim Γ A B) → (S : Stack Γ B C) → Stack Γ A C

-- Weakening of stacks

renˢ : Ren Γ′ Γ → Stack Γ A B → Stack Γ′ A B
renˢ ρ ε = ε
renˢ ρ (e ∙ S) = renᵉ ρ e ∙ renˢ ρ S

ren1ˢ : (𝓐 : ConItem C) → Stack Γ A B → Stack (Γ ∙ 𝓐) A B
ren1ˢ _ = renˢ (stepRen idRen)

ren2ˢ : Stack Γ A B → Stack (Γ ∙ 𝓒 ∙ 𝓓) A B
ren2ˢ = renˢ (stepRen (stepRen idRen))

private
  variable
    S S′ : Stack _ _ _
    e e′ : Elim _ _ _

renˢ-ε : {S : Stack _ A _}
       → renˢ ρ S ≡ ε
       → S ≡ ε
renˢ-ε {S = ε} refl = refl

renˢ-∙ : {Sₗ : Stack _ A _}
       → renˢ ρ Sₗ ≡ e ∙ S
       → ∃₂ λ e′ S′ → Sₗ ≡ e′ ∙ S′ × renᵉ ρ e′ ≡ e × renˢ ρ S′ ≡ S
renˢ-∙ {Sₗ = _ ∙ _} refl = _ , _ , refl , refl , refl

-- Concatenation of stacks

_++S_ : (S : Stack Γ A B) (S′ : Stack Γ B C) → Stack Γ A C
ε ++S S′ = S′
(e ∙ S) ++S S′ = e ∙ (S ++S S′)

-- Multiplicity of a stack, representing how many copies are currently being evaluated

∣_∣ᵉ : Elim Γ A B → M
∣ (-∘ₑ _) _      ∣ᵉ = 𝟙
∣ (_ ∘⟨ p ⟩ₑ-) _ ∣ᵉ = p
∣ sucₑ           ∣ᵉ = 𝟙
∣ !-ₑ            ∣ᵉ = ω
∣ ⟨-, _ ⟩ₑ _     ∣ᵉ = 𝟙
∣ ⟨ _ ,-⟩ₑ _     ∣ᵉ = 𝟙
∣ let⋆[-]ₑ _ _   ∣ᵉ = 𝟙
∣ let![-]ₑ _ _   ∣ᵉ = 𝟙
∣ let⊗[-]ₑ _ _   ∣ᵉ = 𝟙
∣ linearlyₑ _    ∣ᵉ = 𝟙
∣ consumeₑ       ∣ᵉ = 𝟙
∣ duplicateₑ     ∣ᵉ = 𝟙
∣ new₁ₑ _ _      ∣ᵉ = 𝟙
∣ new₂ₑ _        ∣ᵉ = 𝟙
∣ read₁ₑ _ _     ∣ᵉ = 𝟙
∣ read₂ₑ _       ∣ᵉ = 𝟙
∣ write₁ₑ _ _ _  ∣ᵉ = ω
∣ write₂ₑ _ _ _  ∣ᵉ = 𝟙
∣ write₃ₑ _ _    ∣ᵉ = 𝟙
∣ freeₑ          ∣ᵉ = 𝟙

∣_∣ : Stack Γ A B → M
∣ ε ∣ = 𝟙
∣ e ∙ S ∣ = ∣ S ∣ · ∣ e ∣ᵉ

------------------------------------------------------------------------
-- Heaps

infixl 24 _∙[_]ₕ_

data HeapObject : Con n → ConItem A → Set ℓ where
  value : Δ ⊢ᵥ A → Ren Γ Δ → HeapObject Γ (var A)
  array : Vec Nat n        → HeapObject Γ ref
  lin   :                    HeapObject Γ (var Lin)
  ↯     :                    HeapObject Γ (var A)

renᵒ : Ren Γ Δ → HeapObject Δ 𝓐 → HeapObject Γ 𝓐
renᵒ ρ (value v E) = value v (ρ • E)
renᵒ ρ (array xs)  = array xs
renᵒ ρ lin         = lin
renᵒ ρ ↯           = ↯

ren1ᵒ : HeapObject Γ 𝓐 → HeapObject (Γ ∙ 𝓑) 𝓐
ren1ᵒ = renᵒ (stepRen idRen)

data Heap : Con n → Set ℓ where
  ε       : Heap ε
  _∙[_]ₕ_ : Heap Γ
          → M
          → HeapObject Γ 𝓐
          → Heap (Γ ∙ 𝓐)

-- pattern _∙[_]_ H p o = consₕ H p o

private
  variable
    E E′ : Ren _ _
    o o′ o″ : HeapObject _ _
    v : _ ⊢ᵥ _
    γ δ : Conₘ n
    H H′ H″ : Heap Γ
    x : Γ ∋ᶜ 𝓐

-- Heap variable lookup (with grade update)
-- Note that lookup fails e.g. when the grade is 𝟘.

-- infixl 20 _⊢_↦[_]_⨾_

-- data _⊢_↦[_]_⨾_ : (H : Heap Γ) (x : Γ ∋ᶜ 𝓐) (q : M)
--                   (o : HeapObject Γ 𝓐) (H′ : Heap Γ) → Set ℓ where
--   vz : ren1ᵒ o ≡ o′
--      → p - q ≡ r
--      → H ∙[ p ]ₕ o
--      ⊢ vz ↦[ q ] o′
--      ⨾ H ∙[ r ]ₕ o

--   vs[_]_ : ren1ᵒ o ≡ o′
--          → H
--          ⊢ x ↦[ q ] o
--          ⨾ H′

--          → H  ∙[ p ]ₕ o″
--          ⊢ vs x ↦[ q ] o′
--          ⨾ H′ ∙[ p ]ₕ o″

-- -- Heap lookup (without grade update)

-- data _⊢_↦_ : (H : Heap Γ) (x : Γ ∋ᶜ 𝓐)
--              (o : HeapObject Γ 𝓐) → Set ℓ where
--   vz  : ren1ᵒ o ≡ o′
--       → H ∙[ p ]ₕ o ⊢ vz ↦ o′

--   vs[_]_ : ren1ᵒ o ≡ o′
--          → H ⊢ x ↦ o
--          → H  ∙[ p ]ₕ o″ ⊢ vs x ↦ o′

infixl 20 _⊢_↦[_-_]_⨾_

data _⊢_↦[_-_]_⨾_ : (H : Heap Γ) (x : Γ ∋ᶜ 𝓐) (p q : M)
                    (o : HeapObject Γ 𝓐) (H′ : Heap Γ) → Set ℓ where
  vz[_] : ren1ᵒ o ≡ o′
        → p - q ≡ r
        → H ∙[ p ]ₕ o
        ⊢ vz ↦[ p - q ] o′
        ⨾ H ∙[ r ]ₕ o

  vs[_]_ : ren1ᵒ o ≡ o′
         → H
         ⊢ x ↦[ p - q ] o
         ⨾ H′

         → H  ∙[ p′ ]ₕ o″
         ⊢ vs x ↦[ p - q ] o′
         ⨾ H′ ∙[ p′ ]ₕ o″

_⊢_↦_ : Heap Γ → Γ ∋ᶜ 𝓐 → HeapObject Γ 𝓐 → Set ℓ
H ⊢ x ↦ o = ∃ λ p → H ⊢ x ↦[ p - 𝟘 ] o ⨾ H

_⊢_↦[_] : Heap Γ → Γ ∋ᶜ 𝓐 → M → Set ℓ
H ⊢ x ↦[ p ] = ∃ λ o → H ⊢ x ↦[ p - 𝟘 ] o ⨾ H

_⊢_↦[_]_ : Heap Γ → Γ ∋ᶜ 𝓐 → M → HeapObject Γ 𝓐 → Set ℓ
H ⊢ x ↦[ p ] o = H ⊢ x ↦[ p - 𝟘 ] o ⨾ H

_⊢_↦[-_]_⨾_ : Heap Γ → Γ ∋ᶜ 𝓐 → M → HeapObject Γ 𝓐 → Heap Γ → Set ℓ
H ⊢ x ↦[- q ] o ⨾ H′ = ∃ λ p → H ⊢ x ↦[ p - q ] o ⨾ H′

private
  variable
    ref′ : Γ ∋ᶜ ref
    xs xs′ : Vec Nat n

-- Heap array update

syntax HeapUpdate xs H x H′ = H ⊢ x ≔ xs ⨾ H′

data HeapUpdate {n} (xs : Vec Nat n) : (H : Heap Γ) (x : Γ ∋ᶜ ref)
                                       (H′ : Heap Γ) → Set ℓ where
  vz : {xs′ : Vec Nat n}
     → H ∙[ 𝟙 ]ₕ array xs′
     ⊢ vz ≔ xs
     ⨾ H ∙[ 𝟙 ]ₕ array xs

  vs_ : H
      ⊢ ref′ ≔ xs
      ⨾ H′

      → H  ∙[ p ]ₕ o
      ⊢ vs ref′ ≔ xs
      ⨾ H′ ∙[ p ]ₕ o

pattern vz[] p-q≡r = vz[ refl ] p-q≡r
pattern vs[]_ l = vs[ refl ] l

------------------------------------------------------------------------
-- Evaluation states

-- States, indexed by the context of the heap and the context of the head.

infix   2 ⟪_,_,_,_⟫

record State (Γ : Con m) (Δ : Con n) (A B : Type) : Set ℓ where
  constructor ⟪_,_,_,_⟫
  field
    heap  : Heap Γ
    head  : Δ ⊢ A
    env   : Ren Γ Δ
    stack : Stack Γ A B

-- Converting states back to terms

⦅_⦆ᵉ : Elim Γ A B → (Γ ⊢ A → Γ ⊢ B)
⦅  (-∘ₑ u) E ⦆ᵉ t       =        t    ∘ ren E u
⦅ (t ∘ₑ-)  E ⦆ᵉ u       = ren E ⦅ t ⦆ᵛ ∘      u
⦅ sucₑ ⦆ᵉ t             = suc t
⦅ !-ₑ ⦆ᵉ t              = ! t
⦅ ⟨-, u ⟩ₑ E ⦆ᵉ t       = ⟨ t , (ren E u) ⟩
⦅ ⟨ v ,-⟩ₑ E ⦆ᵉ u       = ⟨ ren E ⦅ v ⦆ᵛ , u ⟩
⦅ let⋆[-]ₑ u E ⦆ᵉ t     = let⋆[ t ] (ren E u)
⦅ let![-]ₑ u E ⦆ᵉ t     = let![ t ] (ren (liftRen E) u)
⦅ let⊗[-]ₑ u E ⦆ᵉ t     = let⊗[ t ] ren (liftRen (liftRen E)) u
⦅ linearlyₑ x ⦆ᵉ t      = linearly (ren1 _ t)
⦅ consumeₑ ⦆ᵉ l         = consume l
⦅ duplicateₑ ⦆ᵉ l       = duplicate l
⦅ new₁ₑ l E ⦆ᵉ s        = new (ren E l) s
⦅ new₂ₑ s   ⦆ᵉ l        = new l (Nat→⊢ s)
⦅ read₁ₑ xs   E ⦆ᵉ i    = read (ren E xs)       i
⦅ read₂ₑ    i   ⦆ᵉ xs   = read         xs     (Nat→⊢ i)
⦅ write₁ₑ xs i   E ⦆ᵉ v = write (ren E xs) (ren E i) v
⦅ write₂ₑ xs   v E ⦆ᵉ i = write (ren E xs) i (Nat→⊢ v)
⦅ write₃ₑ    i v ⦆ᵉ xs  = write xs (Nat→⊢ i) (Nat→⊢ v)
⦅ freeₑ ⦆ᵉ t            = free t

⦅_⦆ : Stack Γ A B → (Γ ⊢ A → Γ ⊢ B)
⦅ ε ⦆ = idᶠ
⦅ e ∙ S ⦆ = ⦅ S ⦆ ∘ᶠ ⦅ e ⦆ᵉ

-- Subst : Con m → Con n → Set ℓ
-- Subst Δ Γ = ∀ {A} → Γ ∋ᶜ var A → Δ ⊢ A

-- idSubst : Subst Γ Γ
-- idSubst = `_

-- consSubst : Subst Δ Γ → Δ ⊢ A → Subst Δ (Γ ∙ var A)
-- consSubst σ t vz     = t
-- consSubst σ t (vs x) = σ x

-- toSubstₕ : Heap Γ → Subst ε Γ
-- toSubstₕ ε = idSubst
-- toSubstₕ (H ∙ (_ , t , E)) =
--   let σ = toSubstₕ H
--   in  consSubst σ (wk E t [ σ ])

-- infix 25 _[_]ₕ
-- infix 25 _[_]⇑ₕ

-- _[_]ₕ : Term m → Heap m → Term 0
-- t [ H ]ₕ = t [ toSubstₕ H ]

-- _[_]⇑ₕ : Term (1+ m) → Heap m → Term 1
-- t [ H ]⇑ₕ = t [ liftSubst (toSubstₕ H) ]

-- norm : State Γ A B → Γ ⊢ A
-- norm ⟨ H , t , E , S ⟩ = ⦅ S ⦆ (wk E t) [ H ]ₕ

------------------------------------------------------------------------
-- Usage

-- -- For usage context γ, multiplicity p and q, and closure c,
-- --   γ ⨾ p ▸ᶜ[ q ] c
-- -- means that c is well-resourced in γ
-- data _⨾_▸ᶜ[_]_ (γ : Conₘ n) (p : M) (q : M) :
--                (c : Γ ⊩[ Δ ]⊢ A) → Set ℓ where
--   ▸ᶜ : γ ▸ t
--      → q ≤ p -- required by proof
--      → γ ⨾ p ▸ᶜ[ q ] (t , E)
-- ...
-- data _▸ʰ_ : {Γ : Con n} → Conₘ n → Heap Γ → Set ℓ where
--   ε : ε ▸ʰ ε
--  _∙_ : γ +ᶜ p ·ᶜ wkConₘ E δ ▸ʰ H
--      → δ ⨾ p ▸ᶜ[ q ] (t , E)
--      → γ ∙ p ▸ʰ H ∙[ p ] (t , E)

private
  variable
    v₁ v₂ : _ ⊢ᵥ _

data _▸ᵒ[_]_ {n} {Γ : Con n} : Conₘ n → M → HeapObject Γ 𝓐 → Set ℓ where
  value : γ ▸ ⦅ v ⦆ᵛ
        → renConₘ E γ ▸ᵒ[ p ] value v E
  array𝟘 : 𝟘ᶜ ▸ᵒ[ 𝟘 ] array xs
  array𝟙 : 𝟘ᶜ ▸ᵒ[ 𝟙 ] array xs
  lin𝟘   : 𝟘ᶜ ▸ᵒ[ 𝟘 ] lin
  lin𝟙   : 𝟘ᶜ ▸ᵒ[ 𝟙 ] lin

data _▸ʰ_ : {Γ : Con n} → Conₘ n → Heap Γ → Set ℓ where
  ε   : ε ▸ʰ ε
  _∙_ : γ +ᶜ p ·ᶜ δ ▸ʰ H
      → δ ▸ᵒ[ p ] o
      → γ ∙ p ▸ʰ H ∙[ p ]ₕ o

------------------------------------------------------------------------
-- Usage of eliminators and stacks

-- Usage of eliminators

data _▸ᵉ_ {n : Nat} {Γ : Con n} : (γ : Conₘ n)
                                  (e : Elim Γ A B) → Set ℓ where
  -∘ₑ_ : γ ▸ u
        → p ·ᶜ renConₘ E γ ▸ᵉ (Elim _ _ B ∋ (-∘⟨ p ⟩ₑ u) E)
  _∘ₑ- : γ ▸ ⦅ v ⦆ᵛ
        → renConₘ E γ ▸ᵉ (v ∘⟨ p ⟩ₑ-) E

  sucₑ  : 𝟘ᶜ ▸ᵉ (Elim _ _ ℕ ∋ sucₑ)
  !-ₑ   : 𝟘ᶜ ▸ᵉ (Elim _ _ (! B) ∋ !-ₑ)

  ⟨-,_⟩ₑ : γ ▸ t
         → renConₘ E γ ▸ᵉ (Elim _ _ (A ⊗ _) ∋ ⟨-, t ⟩ₑ E)
  ⟨_,-⟩ₑ : γ ▸ ⦅ v ⦆ᵛ
         → renConₘ E γ ▸ᵉ (Elim _ _ (_ ⊗ B) ∋ ⟨ v ,-⟩ₑ E)

  let⊗[-]ₑ : γ ∙ 𝟙 ∙ 𝟙 ▸ u
          → renConₘ E γ ▸ᵉ let⊗[-]ₑ u E
  let⋆[-]ₑ : γ ▸ u
          → renConₘ E γ ▸ᵉ let⋆[-]ₑ u E
  let![-]ₑ : γ ∙ ω ▸ u
          → renConₘ E γ ▸ᵉ let![-]ₑ u E

  linearlyₑ : γ ▸ ` x
            → γ ▸ᵉ linearlyₑ {A = A} x

  consumeₑ   : 𝟘ᶜ ▸ᵉ consumeₑ
  duplicateₑ : 𝟘ᶜ ▸ᵉ duplicateₑ

  new₁ₑ : γ ▸ t
        → renConₘ E γ ▸ᵉ new₁ₑ t E
  new₂ₑ : 𝟘ᶜ ▸ᵉ new₂ₑ n

  read₁ₑ : γ ▸ t
         → renConₘ E γ ▸ᵉ read₁ₑ t E
  read₂ₑ : renConₘ E γ ▸ᵉ read₂ₑ n

  write₁ₑ : γ ▸ t
          → δ ▸ u
          → renConₘ E (γ +ᶜ δ) ▸ᵉ write₁ₑ t u E
  write₂ₑ : γ ▸ t
          → renConₘ E γ ▸ᵉ write₂ₑ t n E
  write₃ₑ : 𝟘ᶜ ▸ᵉ write₃ₑ n m

  freeₑ : 𝟘ᶜ ▸ᵉ freeₑ

∣e∣≡𝟙 : {e : Elim Γ Arr B}
      → γ ▸ᵉ e
      → ∣ e ∣ᵉ ≡ 𝟙
∣e∣≡𝟙 {e = (f ∘ₑ-) E} (▸f ∘ₑ-) = {! ▸f  !}
∣e∣≡𝟙 {e = !-ₑ} !-ₑ = {!   !}
∣e∣≡𝟙 {e = ⟨-, x ⟩ₑ E} ▸e = refl
∣e∣≡𝟙 {e = ⟨ x ,-⟩ₑ E} ▸e = refl
∣e∣≡𝟙 {e = read₂ₑ x} ▸e = refl
∣e∣≡𝟙 {e = write₃ₑ x E} ▸e = refl
∣e∣≡𝟙 {e = freeₑ} ▸e = refl

-- Usage of stacks.

data _▸ˢ_ {n : Nat} {Γ : Con n} {B} : (γ : Conₘ n) (S : Stack Γ A B) → Set ℓ where
  ε : 𝟘ᶜ ▸ˢ ε
  _∙_ : ∣ S ∣ ·ᶜ δ ▸ᵉ e
      → γ ▸ˢ S
      → γ +ᶜ δ ▸ˢ e ∙ S

------------------------------------------------------------------------
-- Usage of evaluation states.

_⨾_⨾_▸_ : (γ : Conₘ n) (δ : Conₘ m) (η : Conₘ n)
          {Γ : Con n} {Δ : Con m}
          (s : State Γ Δ A B)
        → Set ℓ
γ ⨾ δ ⨾ η ▸ ⟪ H , t , E , S ⟫ =
  γ ▸ʰ H ×
  δ ▸ t ×
  η ▸ˢ S ×
  γ ≤ᶜ ∣ S ∣ ·ᶜ renConₘ E δ +ᶜ η

-- module _ where
--   private
--     variable
--       x : Γ ∋ᶜ var A

--   ▸-heapLookup : H ⊢ x ↦[ q ] value (v , E) ⨾ H′
--                → γ ▸ʰ H
--                → γ ⟨ toFin x ⟩ - q ≤ r
--                → q ≢ 𝟘
--                → ∃ λ δ → δ ▸ ⦅ v ⦆ᵛ × (γ , toFin x ≔ r) +ᶜ q ·ᶜ wkConₘ E δ ▸ʰ H′
--   ▸-heapLookup (here x)  ▸H p-q≤r q≢𝟘 = {!   !}
--   ▸-heapLookup (there x) ▸H p-q≤r q≢𝟘 = {!   !}

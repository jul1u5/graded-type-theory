open import Graded.Modality

module ArrayLang.Usage
  {ℓ} {M : Set ℓ}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Graded.Context 𝕄

open import Agda.Primitive
open import Data.Vec
open import Tools.Nat using (Nat)

open import ArrayLang.Syntax 𝕄

private
  variable
    n : Nat
    p q r : M
    Γ : Con n
    γ δ η : Conₘ n
    A : Type
    𝓐 : ConItem A
    t u v : Γ ⊢ A
    x : Γ ∋ᶜ 𝓐

infix 10 _▸_
data _▸_ {Γ : Con n} : (γ : Conₘ n) → Γ ⊢ A → Set ℓ where
  var       : (𝟘ᶜ , toFin x ≔ 𝟙) ▸ ` x

  lamₘ      : γ ∙ p ▸ t
            → γ ▸ lam p t

  _∘ₘ_      : γ ▸ t
            → δ ▸ u
            → γ +ᶜ p ·ᶜ δ ▸ t ∘⟨ p ⟩ u

  starₘ     : 𝟘ᶜ ▸ star

  let⋆[_]ₘ_ : γ ▸ t
            → δ ▸ u
            → γ +ᶜ δ ▸ let⋆[ t ] u

  ⟨_,_⟩ₘ    : γ ▸ t
            → δ ▸ u
            → γ +ᶜ δ ▸ ⟨ t , u ⟩

  let⊗[_]ₘ_ : γ ▸ t
            → δ ∙ 𝟙 ∙ 𝟙 ▸ u
            → γ +ᶜ δ ▸ let⊗[ t ] u

  zeroₘ     : 𝟘ᶜ ▸ zero
  sucₘ      : γ ▸ t
            → γ ▸ suc t

  !ₘ_       : γ ▸ t
            → ω ·ᶜ γ ▸ ! t

  let![_]ₘ_ : γ ▸ t
            → δ ∙ ω ▸ u
            → γ +ᶜ δ ▸ let![ t ] u

  linearlyₘ  : γ ∙ 𝟙 ▸ t
             → γ     ▸ linearly t
  consumeₘ   : γ ▸ t
             → γ ▸ consume t
  duplicateₘ : γ ▸ t
             → γ ▸ duplicate t

  newₘ   : γ ▸ t
         → δ ▸ u
         → γ +ᶜ δ ▸ new t u

  readₘ  : γ ▸ t
         → δ ▸ u
         → γ +ᶜ δ ▸ read t u

  writeₘ : γ ▸ t
         → δ ▸ u
         → η ▸ v
         → γ +ᶜ δ +ᶜ ω ·ᶜ η ▸ write t u v

  freeₘ  : γ ▸ t
         → γ ▸ free t

  sub : γ ▸ t
      → δ ≤ᶜ γ
      → δ ▸ t

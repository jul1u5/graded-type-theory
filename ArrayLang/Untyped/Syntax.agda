open import Agda.Primitive
open import Graded.Modality

module ArrayLang.Untyped.Syntax
  (ℓ : Level) (M : Set ℓ)
  (𝕄 : Modality M)
  where

open import Tools.Nat

data Term : Nat → Set ℓ where
  zero : Term 𝟘

module Definition.LogicalRelation.Consequences.Canonicity where

open import Definition.Untyped hiding (wk)
import Definition.Untyped as U
open import Definition.Untyped.Properties

open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps

open import Definition.LogicalRelation
import Definition.LogicalRelation.Weakening as LR
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Fundamental

open import Data.Empty
open import Data.Unit
open import Data.Nat.Base renaming (ℕ to Nat)
open import Data.Product

import Relation.Binary.PropositionalEquality as PE


sucᵏ : Nat → Term
sucᵏ zero = zero
sucᵏ (suc n) = suc (sucᵏ n)

canonicity'' : ∀ {t l}
             → ([ℕ] : ε ⊩⟨ l ⟩ℕ ℕ)
             → ε ⊩⟨ l ⟩ t ∷ ℕ / ℕ-intr [ℕ]
             → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity'' {l = l} (noemb (ℕ D)) ℕ[ _ , d , suc , prop ] =
  let a , b = canonicity'' {l = l} (noemb (ℕ D)) prop
  in  suc a , trans (subset*Term (redₜ d)) (suc-cong b)
canonicity'' (noemb (ℕ D)) ℕ[ .zero , d , zero , prop ] = zero , subset*Term (redₜ d)
canonicity'' (noemb (ℕ D)) ℕ[ n , d , ne x , prop ] = ⊥-elim (noNe prop x)
canonicity'' (emb 0<1 x) [t] = canonicity'' x [t]

canonicity' : ∀ {t l}
            → ([ℕ] : ε ⊩⟨ l ⟩ ℕ)
            → ε ⊩⟨ l ⟩ t ∷ ℕ / [ℕ]
            → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity' [ℕ] [t] =
  canonicity'' (ℕ-elim [ℕ]) (irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [t])

canonicity : ∀ {t} → ε ⊢ t ∷ ℕ → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity ⊢t with fundamentalTerm ⊢t
canonicity ⊢t | ε , [ℕ] , [t] =
  let [ℕ]' = proj₁ ([ℕ] {σ = idSubst} ε tt)
      [t]' = irrelevanceTerm'' PE.refl (substIdEq _) [ℕ]' [ℕ]' (proj₁ ([t] ε tt))
  in  canonicity' [ℕ]' [t]'

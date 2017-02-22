module Definition.Conversion.Symmetry where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Conversion
open import Definition.Conversion.InitLemma
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.Conversion.Conversion
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.SingleSubst
open import Definition.Typed.Consequences.Substitution

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  sym~↑ : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ
        → Γ ⊢ t ~ u ↑ A
        → ∃ λ B → Γ ⊢ A ≡ B × Δ ⊢ u ~ t ↑ B
  sym~↑ Γ≡Δ (var x x≡y) =
    let ⊢A = syntacticTerm x
    in  _ , refl ⊢A
     ,  var (PE.subst (λ y → _ ⊢ var y ∷ _) x≡y (stabilityTerm Γ≡Δ x))
            (PE.sym x≡y)
  sym~↑ Γ≡Δ (app t~u x) =
    let [ ⊢Γ , ⊢Δ , _ ] = substx Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
        F' , G' , ΠF'G'≡B = Π≡A A≡B whnfB
        F≡F' , G≡G' = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) ΠF'G'≡B A≡B)
    in  _ , substTypeEq G≡G' (soundnessConv↑Term x)
    ,   app (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) ΠF'G'≡B u~t)
            (convConvTerm (symConv↑Term Γ≡Δ x) (stabilityEq Γ≡Δ F≡F'))
  sym~↑ Γ≡Δ (natrec x x₁ x₂ t~u) =
    let [ ⊢Γ , ⊢Δ , _ ] = substx Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
        B≡ℕ = ℕ≡A A≡B whnfB
        F≡G = stabilityEq (Γ≡Δ ∙ refl (ℕ ⊢Γ)) (soundnessConv↑ x)
        F[0]≡G[0] = substTypeEq F≡G (refl (zero ⊢Δ))
    in  _ , substTypeEq (soundnessConv↑ x) (soundness~↓ t~u)
    ,   natrec (symConv↑ (Γ≡Δ ∙ (refl (ℕ ⊢Γ))) x)
               (convConvTerm (symConv↑Term Γ≡Δ x₁) F[0]≡G[0])
               (convConvTerm (symConv↑Term Γ≡Δ x₂) (sucCong F≡G))
               (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ℕ u~t)

  sym~↓ : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t ~ u ↓ A
         → ∃ λ B → Whnf B × Γ ⊢ A ≡ B × Δ ⊢ u ~ t ↓ B
  sym~↓ Γ≡Δ ([~] A₁ D whnfA k~l) =
    let B , A≡B , k~l' = sym~↑ Γ≡Δ k~l
        _ , ⊢B = syntacticEq A≡B
        B' , whnfB' , D' = fullyReducible ⊢B
        A≡B' = trans (sym (subset* D)) (trans A≡B (subset* (red D')))
    in  B' , whnfB' , A≡B' , [~] B (stabilityRed* Γ≡Δ (red D')) whnfB' k~l'

  symConv↑ : ∀ {A B Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A [conv↑] B → Δ ⊢ B [conv↑] A
  symConv↑ Γ≡Δ ([↑] A' B' D D' whnfA' whnfB' A'<>B') =
    [↑] B' A' (stabilityRed* Γ≡Δ D') (stabilityRed* Γ≡Δ D) whnfB' whnfA'
        (symConv↓ Γ≡Δ A'<>B')

  symConv↓ : ∀ {A B Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A [conv↓] B → Δ ⊢ B [conv↓] A
  symConv↓ Γ≡Δ (U-refl x) =
    let [ _ , ⊢Δ , _ ] = substx Γ≡Δ
    in  U-refl ⊢Δ
  symConv↓ Γ≡Δ (ℕ-refl x) =
    let [ _ , ⊢Δ , _ ] = substx Γ≡Δ
    in  ℕ-refl ⊢Δ
  symConv↓ Γ≡Δ (ne A~B) =
    let B , whnfB , U≡B , B~A = sym~↓ Γ≡Δ A~B
        B≡U = U≡A U≡B
    in  ne (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡U B~A)
  symConv↓ Γ≡Δ (Π-cong x A<>B A<>B₁) =
    let F≡H = soundnessConv↑ A<>B
        _ , ⊢H = syntacticEq (stabilityEq Γ≡Δ F≡H)
    in  Π-cong ⊢H (symConv↑ Γ≡Δ A<>B)
                  (symConv↑ (Γ≡Δ ∙ F≡H) A<>B₁)

  symConv↑Term : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t [conv↑] u ∷ A → Δ ⊢ u [conv↑] t ∷ A
  symConv↑Term Γ≡Δ ([↑]ₜ B t' u' D d d' whnfB whnft' whnfu' t<>u) =
    [↑]ₜ B u' t' (stabilityRed* Γ≡Δ D) (stabilityRed*Term Γ≡Δ d')
         (stabilityRed*Term Γ≡Δ d) whnfB whnfu' whnft' (symConv↓Term Γ≡Δ t<>u)

  symConv↓Term : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t [conv↓] u ∷ A → Δ ⊢ u [conv↓] t ∷ A
  symConv↓Term Γ≡Δ (ℕ-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
        B≡ℕ = ℕ≡A A≡B whnfB
    in  ℕ-ins (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ℕ u~t)
  symConv↓Term Γ≡Δ (ne-ins t u x t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
    in  ne-ins (stabilityTerm Γ≡Δ u) (stabilityTerm Γ≡Δ t) x u~t
  symConv↓Term Γ≡Δ (univ x x₁ x₂) =
    univ (stabilityTerm Γ≡Δ x₁) (stabilityTerm Γ≡Δ x) (symConv↓ Γ≡Δ x₂)
  symConv↓Term Γ≡Δ (zero-refl x) =
    let [ _ , ⊢Δ , _ ] = substx Γ≡Δ
    in  zero-refl ⊢Δ
  symConv↓Term Γ≡Δ (suc-cong t<>u) = suc-cong (symConv↑Term Γ≡Δ t<>u)
  symConv↓Term Γ≡Δ (fun-ext x x₁ x₂ y y₁ t<>u) =
    fun-ext (stability Γ≡Δ x) (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₁)
            y₁ y (symConv↑Term (Γ≡Δ ∙ refl x) t<>u)

symConv : ∀ {A B Γ} → Γ ⊢ A [conv↑] B → Γ ⊢ B [conv↑] A
symConv A<>B =
  let ⊢Γ = wfEq (soundnessConv↑ A<>B)
  in  symConv↑ (reflConEq ⊢Γ) A<>B

symConvTerm : ∀ {t u A Γ} → Γ ⊢ t [conv↑] u ∷ A → Γ ⊢ u [conv↑] t ∷ A
symConvTerm t<>u =
  let ⊢Γ = wfEqTerm (soundnessConv↑Term t<>u)
  in  symConv↑Term (reflConEq ⊢Γ) t<>u

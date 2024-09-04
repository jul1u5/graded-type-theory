------------------------------------------------------------------------
-- Properties of neutral terms and WHNFs
------------------------------------------------------------------------

open import Definition.Typed.Variant

module Definition.Untyped.Properties.Neutral
  {a}
  (M : Set a)
  (type-variant : Type-variant)
  where

open import Tools.Function
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum hiding (sym)

open import Definition.Untyped M
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant

private variable
  t u : Term _
  ρ : Wk _ _
  σ : Subst _ _

opaque

  -- Being a numeral is preserved under weakening

  wk-numeral : Numeral t → Numeral (wk ρ t)
  wk-numeral zeroₙ = zeroₙ
  wk-numeral (sucₙ n) = sucₙ (wk-numeral n)

opaque

  neutral-subst : Neutral (t [ σ ]) → Neutral t
  neutral-subst n = lemma n refl
    where
    open import Tools.Product
    lemma : Neutral u → t [ σ ] ≡ u → Neutral t
    lemma {t} (var x) ≡u =
      case subst-var {t = t} ≡u of λ {
        (x , refl , ≡t′) →
      var x }
    lemma {t} (∘ₙ n) ≡u =
      case subst-∘ {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , refl , ≡t′ , _)) →
      ∘ₙ (lemma n ≡t′)}
    lemma {t} (fstₙ n) ≡u =
      case subst-fst {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , refl , ≡t′)) →
      fstₙ (lemma n ≡t′) }
    lemma {t} (sndₙ n) ≡u =
      case subst-snd {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , refl , ≡t′)) →
      sndₙ (lemma n ≡t′) }
    lemma {t} (natrecₙ n) ≡u =
      case subst-natrec {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , _ , refl , _ , _ , _ , ≡t′)) →
      natrecₙ (lemma n ≡t′) }
    lemma {t} (prodrecₙ n) ≡u =
      case subst-prodrec {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , refl , _ , ≡t′ , _)) →
      prodrecₙ (lemma n ≡t′) }
    lemma {t} (emptyrecₙ n) ≡u =
      case subst-emptyrec {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , refl , _ , ≡t′)) →
      emptyrecₙ (lemma n ≡t′) }
    lemma {t} (unitrecₙ no-η n) ≡u =
      case subst-unitrec {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , refl , _ , ≡t′ , _)) →
      unitrecₙ no-η (lemma n ≡t′) }
    lemma {t} (Jₙ n) ≡u =
      case subst-J {w = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , _ , _ , _ , refl , _ , _ , _ , _ , _ , ≡t′)) →
      Jₙ (lemma n ≡t′) }
    lemma {t} (Kₙ n) ≡u =
      case subst-K {w = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , _ , _ , refl , _ , _ , _ , _ , ≡t′)) →
      Kₙ (lemma n ≡t′) }
    lemma {t} ([]-congₙ n) ≡u =
      case subst-[]-cong {w = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , _ , refl , _ , _ , _ , ≡t′)) →
      []-congₙ (lemma n ≡t′) }


opaque

  -- Not being in Whnf is preseved by substitutions

  ¬whnf-subst : ¬ Whnf t → ¬ Whnf (t [ σ ])
  ¬whnf-subst ¬w w = lemma ¬w refl w
    where
    open import Tools.Product
    lemma : ¬ Whnf t → t [ σ ] ≡ u → ¬ Whnf u
    lemma {t} ¬w ≡u Uₙ =
      case subst-U {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ refl) → ¬w Uₙ}
    lemma {t} ¬w ≡u ΠΣₙ =
      case subst-ΠΣ {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ (_ , _ , refl , _)) → ¬w ΠΣₙ}
    lemma {t} ¬w ≡u ℕₙ =
      case subst-ℕ {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ refl) → ¬w ℕₙ}
    lemma {t} ¬w ≡u Unitₙ =
      case subst-Unit {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ refl) → ¬w Unitₙ}
    lemma {t} ¬w ≡u Emptyₙ =
      case subst-Empty {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ refl) → ¬w Emptyₙ}
    lemma {t} ¬w ≡u Idₙ =
      case subst-Id {v = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ (_ , _ , _ , refl , _)) → ¬w Idₙ}
    lemma {t} ¬w ≡u lamₙ =
      case subst-lam {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ (_ , refl , _)) → ¬w lamₙ}
    lemma {t} ¬w ≡u zeroₙ =
      case subst-zero {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ refl) → ¬w zeroₙ}
    lemma {t} ¬w ≡u sucₙ =
      case subst-suc {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ (_ , refl , _)) → ¬w sucₙ}
    lemma {t} ¬w ≡u starₙ =
      case subst-star {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ refl) → ¬w starₙ}
    lemma {t} ¬w ≡u prodₙ =
      case subst-prod {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ (_ , _ , refl , _)) → ¬w prodₙ}
    lemma {t} ¬w ≡u rflₙ =
      case subst-rfl {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → ¬w (ne (var _));
        (inj₂ refl) → ¬w rflₙ}
    lemma ¬w ≡u (ne n) =
      ¬w (ne (neutral-subst (subst Neutral (sym ≡u) n)))

------------------------------------------------------------------------
-- Torus
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

module Space.Torus where

open import Prelude

open import Path
open import Path.Lemmas
open import Path.Symbol

import Space.Sphere as S

private
  data T²′ : Set where
    base′ : T²′

T² : Set
T² = T²′

base : T²
base = base′

postulate
  loopα : base ≡ base
  loopβ : base ≡ base
  cell : loopα ◇ loopβ ≡ loopβ ◇ loopα

T²-elim : ∀ {ℓ} (P : T² → Set ℓ) (pbase : P base)
          (ploopα : subst P loopα pbase ≡ pbase)
          (ploopβ : subst P loopβ pbase ≡ pbase)
          (pcell : subst (λ p → subst P p pbase ≡ pbase) cell
             (subst-trans P loopα loopβ pbase ◇ cong (subst P loopβ) ploopα ◇ ploopβ) ≡
             (subst-trans P loopβ loopα pbase ◇ cong (subst P loopα) ploopβ ◇ ploopα)) →
          ∀ x → P x
T²-elim _ pbase′ _ _ _ base′ = pbase′

cong[dep]-trans : ∀ {ℓ₁} {ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) (f : (x : A) → B x)
  {x y} (loop₁ : x ≡ y) {z} (loop₂ : y ≡ z) →
  cong[dep] B f (loop₁ ◇ loop₂) ≡
  subst-trans B loop₁ loop₂ (f x) ◇ cong (subst B loop₂) (cong[dep] B f loop₁) ◇ cong[dep] B f loop₂
cong[dep]-trans B f {x} =
  elim′
    (λ {y} p₁ → ∀ {z} (p₂ : y ≡ z) →
      cong[dep] B f (p₁ ◇ p₂) ≡
      subst-trans B p₁ p₂ (f x) ◇ cong (subst B p₂) (cong[dep] B f p₁) ◇ cong[dep] B f p₂)
    (elim′
      (λ {z} p₂ → 
        cong[dep] B f p₂ ≡
        subst-trans B (refl _) p₂ (f x) ◇ cong[dep] B f p₂)
      (refl _))

cong[dep]-trans′ : ∀ {ℓ₁} {ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) (f : (x : A) → B x)
  {x y} (loop₁ : x ≡ y) {z} (loop₂ : y ≡ z)
  {bloop₁} (bloop₁-eq : cong[dep] B f loop₁ ≡ bloop₁)
  {bloop₂} (bloop₂-eq : cong[dep] B f loop₂ ≡ bloop₂) →
  cong[dep] B f (loop₁ ◇ loop₂) ≡
  subst-trans B loop₁ loop₂ (f x) ◇ cong (subst B loop₂) bloop₁ ◇ bloop₂
cong[dep]-trans′ B f {x} =
  elim′
    (λ {y} p₁ → ∀ {z} (p₂ : y ≡ z) {bp₁} (bp₁-eq : cong[dep] B f p₁ ≡ bp₁) {bp₂} (bp₂-eq : cong[dep] B f p₂ ≡ bp₂) →
      cong[dep] B f (p₁ ◇ p₂) ≡
      subst-trans B p₁ p₂ (f x) ◇ cong (subst B p₂) bp₁ ◇ bp₂)
    (elim′
      (λ {z} p₂ → ∀ {bp₁} (bp₁-eq : refl (f x) ≡ bp₁) {bp₂} (bp₂-eq : cong[dep] B f p₂ ≡ bp₂) →
        cong[dep] B f p₂ ≡
        cong (subst B p₂) bp₁ ◇ bp₂)
      (λ {bp₁} bp₁-eq {bp₂} bp₂-eq →
        bp₂-eq ◇ cong (λ p → p ◇ bp₂) (bp₁-eq ◇ sym (cong-id bp₁))))

postulate
  T²-elim-loopα : ∀ {ℓ} (P : T² → Set ℓ) (pbase : P base)
                  (ploopα : subst P loopα pbase ≡ pbase)
                  (ploopβ : subst P loopβ pbase ≡ pbase)
                  (pcell : subst (λ p → subst P p pbase ≡ pbase) cell
                    (subst-trans P loopα loopβ pbase ◇ cong (subst P loopβ) ploopα ◇ ploopβ) ≡
                    (subst-trans P loopβ loopα pbase ◇ cong (subst P loopα) ploopβ ◇ ploopα)) →
                  cong[dep] P (T²-elim P pbase ploopα ploopβ pcell) loopα ≡ ploopα

  T²-elim-loopβ : ∀ {ℓ} (P : T² → Set ℓ) (pbase : P base)
                  (ploopα : subst P loopα pbase ≡ pbase)
                  (ploopβ : subst P loopβ pbase ≡ pbase)
                  (pcell : subst (λ p → subst P p pbase ≡ pbase) cell
                    (subst-trans P loopα loopβ pbase ◇ cong (subst P loopβ) ploopα ◇ ploopβ) ≡
                    (subst-trans P loopβ loopα pbase ◇ cong (subst P loopα) ploopβ ◇ ploopα)) →
                  cong[dep] P (T²-elim P pbase ploopα ploopβ pcell) loopβ ≡ ploopβ

  T²-elim-cell : ∀ {ℓ} (P : T² → Set ℓ) (pbase : P base)
                   (ploopα : subst P loopα pbase ≡ pbase)
                   (ploopβ : subst P loopβ pbase ≡ pbase)
                   (pcell : subst (λ p → subst P p pbase ≡ pbase) cell
                     (subst-trans P loopα loopβ pbase ◇ cong (subst P loopβ) ploopα ◇ ploopβ) ≡
                     (subst-trans P loopβ loopα pbase ◇ cong (subst P loopα) ploopβ ◇ ploopα)) →
                   let
                     eliminator = T²-elim P pbase ploopα ploopβ pcell
                     elim-loopα = T²-elim-loopα P pbase ploopα ploopβ pcell
                     elim-loopβ = T²-elim-loopβ P pbase ploopα ploopβ pcell
                     convertαβ = cong[dep]-trans′ P eliminator loopα loopβ elim-loopα elim-loopβ
                     convertβα = cong[dep]-trans′ P eliminator loopβ loopα elim-loopβ elim-loopα
                   in 
                     cong (subst (λ p → subst P p pbase ≡ pbase) cell) (sym convertαβ) ◇
                     cong[dep] (λ p → subst P p pbase ≡ pbase) (cong[dep] P eliminator) cell ◇
                     convertβα ≡
                     pcell

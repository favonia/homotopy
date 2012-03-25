------------------------------------------------------------------------
-- Spheres (two-point version)
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

-- Currently we have S¹ and an experimental S²

{-# OPTIONS --without-K #-}

module Space.Sphere-alternative where

open import Prelude
open import Path
open import Path.Lemmas

------------------------------------------------------------------------
-- Formation rules and introduction rules

private
  data S′¹′ : Set where
    north⁰′ : S′¹′
    south⁰′ : S′¹′

S′¹ : Set
S′¹ = S′¹′

north⁰ : S′¹
north⁰ = north⁰′

south⁰ : S′¹
south⁰ = south⁰′

postulate
  north¹ : south⁰ ≡ north⁰
  south¹ : north⁰ ≡ south⁰

------------------------------------------------------------------------
-- Elimination rules and computation rules

-- Dependent version

S′¹-elim : ∀ {ℓ} (P : S′¹ → Set ℓ) (pnorth⁰ : P north⁰) (psouth⁰ : P south⁰) →
          subst P north¹ psouth⁰ ≡ pnorth⁰ → subst P south¹ pnorth⁰ ≡ psouth⁰ →
          (x : S′¹) → P x
S′¹-elim _ pnorth⁰ _ _ _ north⁰′ = pnorth⁰
S′¹-elim _ _ psouth⁰ _ _ south⁰′ = psouth⁰

-- They are actually definitionally equal...
postulate
  S′¹-elim-north¹ : ∀ {ℓ} (P : S′¹ → Set ℓ) (pnorth⁰ : P north⁰) (psouth⁰ : P south⁰)
                    (pnorth¹ : subst P north¹ psouth⁰ ≡ pnorth⁰)
                    (psouth¹ : subst P south¹ pnorth⁰ ≡ psouth⁰) →
                    cong[dep] P (S′¹-elim P pnorth⁰ psouth⁰ pnorth¹ psouth¹) north¹ ≡ pnorth¹
  S′¹-elim-south¹ : ∀ {ℓ} (P : S′¹ → Set ℓ) (pnorth⁰ : P north⁰) (psouth⁰ : P south⁰) →
                    (pnorth¹ : subst P north¹ psouth⁰ ≡ pnorth⁰)
                    (psouth¹ : subst P south¹ pnorth⁰ ≡ psouth⁰) →
                    cong[dep] P (S′¹-elim P pnorth⁰ psouth⁰ pnorth¹ psouth¹) south¹ ≡ psouth¹

-- Non-dependent version

S′¹-elim[simp] : ∀ {ℓ} {P : Set ℓ} (pnorth psouth : P) → psouth ≡ pnorth → pnorth ≡ psouth → S′¹ → P
S′¹-elim[simp] {P = P} pn ps pn¹ ps¹ = S′¹-elim (const P) pn ps (trans boring-n¹ pn¹) (trans boring-s¹ ps¹)
  where
    boring-n¹ = subst-const north¹ ps
    boring-s¹ = subst-const south¹ pn

-- This propositional equality is derivable from the dependent version.
postulate
  S′¹-elim[simp]-north¹ : ∀ {ℓ} {P : Set ℓ} (pnorth⁰ psouth⁰ : P)
                          (pnorth¹ : psouth⁰ ≡ pnorth⁰)
                          (psouth¹ : pnorth⁰ ≡ psouth⁰) →
                          cong (S′¹-elim[simp] pnorth⁰ psouth⁰ pnorth¹ psouth¹) north¹ ≡ pnorth¹
  S′¹-elim[simp]-south¹ : ∀ {ℓ} {P : Set ℓ} (pnorth⁰ psouth⁰ : P) →
                          (pnorth¹ : psouth⁰ ≡ pnorth⁰)
                          (psouth¹ : pnorth⁰ ≡ psouth⁰) →
                          cong (S′¹-elim[simp] pnorth⁰ psouth⁰ pnorth¹ psouth¹) south¹ ≡ psouth¹

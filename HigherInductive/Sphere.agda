------------------------------------------------------------------------
-- Spheres.
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

-- Currently we have S¹ and an experimental S²

{-# OPTIONS --without-K #-}

module HigherInductive.Sphere where

open import Prelude
open import Path
open import Path.Lemmas

------------------------------------------------------------------------
-- Formation rules and introduction rules

private
  data S¹′ : Set where
    base¹′ : S¹′

S¹ : Set
S¹ = S¹′

base¹ : S¹
base¹ = base¹′

base : S¹
base = base¹

-- Agda seems to think loop and refl are NOT definitionally equal
-- outside of this abstract block
abstract
  loop¹ : base¹ ≡ base¹
  loop¹ = refl base¹

loop : base ≡ base
loop = loop¹

------------------------------------------------------------------------
-- Elimination rules and computation rules

-- Dependent version

S¹-elim : ∀ {ℓ} (P : S¹ → Set ℓ) (dbase : P base) → subst P loop¹ dbase ≡ dbase → (x : S¹) → P x
S¹-elim _ dbase _ base¹′ = dbase

-- This is actually definitionally equality...
postulate
  S¹-elim-loop : ∀ {ℓ} (P : S¹ → Set ℓ) (dbase : P base) (dloop : subst P loop¹ dbase ≡ dbase)
                 → cong[dep] P (S¹-elim P dbase dloop) loop¹ ≡ dloop

-- Non-dependent version

S¹-elim[simp] : ∀ {ℓ} {P : Set ℓ} (dbase : P) → dbase ≡ dbase → S¹ → P
S¹-elim[simp] {P = P} dbase dloop = S¹-elim (const P) dbase (trans boring-loop dloop)
  where
    boring-loop = subst-const loop dbase

-- This propositional equality is derivable from the dependent version.
S¹-elim[simp]-loop : ∀ {ℓ} {P : Set ℓ} (dbase : P) (dloop : dbase ≡ dbase)
                         → cong (S¹-elim[simp] dbase dloop) loop¹ ≡ dloop
S¹-elim[simp]-loop {P = P} dbase dloop =
  cong dcircle loop¹                                                  ≡⟨ sym $ trans-sym-trans boring-loop _ ⟩
  trans (sym $ boring-loop) (trans boring-loop $ cong dcircle loop¹)  ≡⟨ cong (trans $ sym $ boring-loop) $ sym $ cong[dep]-const dcircle loop¹ ⟩
  trans (sym $ boring-loop) (cong[dep] (const P) dcircle loop¹)       ≡⟨ cong (trans $ sym $ boring-loop) $ S¹-elim-loop (const P) _ _ ⟩
  trans (sym $ boring-loop) (trans boring-loop dloop)                 ≡⟨ trans-sym-trans boring-loop _ ⟩∎
  dloop                                                               ∎
  where
    boring-loop = subst-const loop¹ dbase
    dcircle = S¹-elim[simp] dbase dloop

------------------------------------------------------------------------
-- WARNING : S² is still experimental

------------------------------------------------------------------------
-- Formation rules and introduction rules

private
  data S²′ : Set where
    base²′ : S²′

S² : Set
S² = S²′

base² : S²
base² = base²′

-- Agda seems to think these are NOT definitionally equal
abstract
  loop² : refl base² ≡ refl base²
  loop² = refl (refl base²)

------------------------------------------------------------------------
-- Elimination rules and computation rules

-- Dependent version

S²-elim : ∀ {ℓ} (P : S² → Set ℓ) (dbase : P base²) → subst (λ p → subst P p dbase ≡ dbase) loop² (refl dbase) ≡ refl dbase → (x : S²) → P x
S²-elim _ dbase _ base²′ = dbase

-- This is actually definitionally equality...
postulate
  S²-elim-loop : ∀ {ℓ} (P : S² → Set ℓ) (dbase : P base²) (dloop : subst (λ p → subst P p dbase ≡ dbase) loop² (refl dbase) ≡ refl dbase) →
                 cong[dep] (λ p → subst P p dbase ≡ dbase) (cong[dep] P (S²-elim P dbase dloop)) loop² ≡ dloop

-- Non-dependent version

S²-elim[simp] : ∀ {ℓ} {P : Set ℓ} (dbase : P) → refl dbase ≡ refl dbase → S² → P
S²-elim[simp] {P = P} dbase dloop = S²-elim (const P) dbase (trans boring-loop dloop)
  where
    boring-loop = cong[dep] (λ p → subst (const P) p dbase ≡ dbase) (λ p → subst-const p dbase) loop²

-- TODO This rule should be derivable from the dependent one
postulate
  S²-elim[simp]-loop : ∀ {ℓ} {P : Set ℓ} (dbase : P) (dloop : refl dbase ≡ refl dbase)
                       → cong (cong (S²-elim[simp] dbase dloop)) loop² ≡ dloop

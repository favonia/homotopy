------------------------------------------------------------------------
-- Spheres.
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

-- Currently we only have S¹

{-# OPTIONS --without-K #-}

module HigherInductive.Sphere where

open import Prelude
open import Path
open import Path.Lemmas

------------------------------------------------------------------------
-- Formation rules and introduction rules

private
  data S¹′ : Set where
    base′ : S¹′

S¹ : Set
S¹ = S¹′

base : S¹
base = base′

-- Agda will think loop and refl are NOT definitionally equal
-- outside of this abstract block
abstract
  loop : base′ ≡ base′
  loop = refl base′

------------------------------------------------------------------------
-- Elimination rules and computation rules

-- Dependent version

S¹-elim : ∀ {ℓ} (P : S¹ → Set ℓ) (dbase : P base) → subst P loop dbase ≡ dbase → (x : S¹) → P x
S¹-elim _ dbase _ base′ = dbase

-- This is actually definitionally equality...
postulate
  cong[dep]-S¹-elim-loop : ∀ {ℓ} (P : S¹ → Set ℓ) (dbase : P base) (dloop : subst P loop dbase ≡ dbase)
                          → cong[dep] P (S¹-elim P dbase dloop) loop ≡ dloop

-- Non-dependent version

S¹-elim[simp] : ∀ {ℓ} {P : Set ℓ} (dbase : P) → dbase ≡ dbase → S¹ → P
S¹-elim[simp] {P = P} dbase dloop = S¹-elim (const P) dbase (trans (subst-const loop dbase) dloop)

-- The propositional equality is derivable from the dependent version.
cong-S¹-elim[simp]-loop : ∀ {ℓ} {P : Set ℓ} (dbase : P) (dloop : dbase ≡ dbase)
                         → cong (S¹-elim[simp] dbase dloop) loop ≡ dloop
cong-S¹-elim[simp]-loop {P = P} dbase dloop =
  cong dcircle loop                                                 ≡⟨ sym $ trans-sym-trans boring-loop _ ⟩
  trans (sym $ boring-loop) (trans boring-loop $ cong dcircle loop) ≡⟨ cong (trans $ sym $ boring-loop) $ sym $ cong[dep]-const dcircle loop ⟩
  trans (sym $ boring-loop) (cong[dep] (const P) dcircle loop)      ≡⟨ cong (trans $ sym $ boring-loop) $ cong[dep]-S¹-elim-loop (const P) _ _ ⟩
  trans (sym $ boring-loop) (trans boring-loop dloop)               ≡⟨ trans-sym-trans boring-loop _ ⟩∎
  dloop                                                             ∎
  where
    boring-loop = subst-const loop dbase
    dcircle = S¹-elim[simp] dbase dloop

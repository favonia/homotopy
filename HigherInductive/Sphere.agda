------------------------------------------------------------------------
-- Spheres.
------------------------------------------------------------------------

-- Currently we only have S¹

{-# OPTIONS --without-K #-}

open import Prelude
open import Equality

module HigherInductive.Sphere
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
import Equality.Tactic; open Equality.Tactic eq
import Equality.Misc; open Equality.Misc eq

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
-- Elimination rules

-- Dependent version
S¹-rec : ∀ {ℓ} (P : S¹ → Set ℓ) (dbase : P base) → subst P loop dbase ≡ dbase → (x : S¹) → P x
S¹-rec _ dbase _ base′ = dbase

-- Non-dependent version
S¹-rec[simp] : ∀ {ℓ} {P : Set ℓ} (dbase : P) → dbase ≡ dbase → S¹ → P
S¹-rec[simp] {P = P} dbase dloop = S¹-rec (const P) dbase (trans (subst-const loop dbase) dloop)

------------------------------------------------------------------------
-- Computation rules

-- Dependent version
-- This is actually definitionally equality...
postulate
  cong[dep]-S¹-rec-loop : ∀ {ℓ} (P : S¹ → Set ℓ) (dbase : P base) (dloop : subst P loop dbase ≡ dbase)
                          → cong[dep] P (S¹-rec P dbase dloop) loop ≡ dloop

-- Non-dependent version
-- The propositional equality is derivable from the dependent version.
cong-S¹-rec[simp]-loop : ∀ {ℓ} {P : Set ℓ} (dbase : P) (dloop : dbase ≡ dbase)
                         → cong (S¹-rec[simp] dbase dloop) loop ≡ dloop
cong-S¹-rec[simp]-loop {P = P} dbase dloop =
  cong dcircle loop                                                 ≡⟨ sym $ trans-reflˡ _ ⟩
  trans (refl _) (cong dcircle loop)                                ≡⟨ cong (λ p → trans p (cong dcircle loop)) $ sym $ trans-symˡ _ ⟩
  trans (trans (sym $ boring-loop) boring-loop) (cong dcircle loop) ≡⟨ trans-assoc _ _ _ ⟩
  trans (sym $ boring-loop) (trans boring-loop $ cong dcircle loop) ≡⟨ cong (trans $ sym $ boring-loop) $ sym $ cong[dep]-nondep dcircle loop ⟩
  trans (sym $ boring-loop) (cong[dep] (const P) dcircle loop)      ≡⟨ cong (trans _) $ cong[dep]-S¹-rec-loop (const P) _ _ ⟩
  trans (sym $ boring-loop) (trans boring-loop dloop)               ≡⟨ sym $ trans-assoc _ _ _ ⟩
  trans (trans (sym $ boring-loop) boring-loop) dloop               ≡⟨ cong (λ p → trans p dloop) $ trans-symˡ _ ⟩
  trans (refl _) dloop                                              ≡⟨ trans-reflˡ _ ⟩∎
  dloop                                                             ∎
  where
    boring-loop = subst-const loop dbase
    dcircle = S¹-rec[simp] dbase dloop

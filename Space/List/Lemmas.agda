------------------------------------------------------------------------
-- Lemmas for List
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

module Space.List.Lemmas where

open import Prelude
open import Path

snoc : ∀ {ℓ} {A : Set ℓ} → List A → A → List A
snoc [] x = x ∷ []
snoc (x ∷ xs) v = x ∷ snoc xs v

rev : ∀ {ℓ} {A : Set ℓ} → List A → List A
rev [] = []
rev (x ∷ xs) = snoc (rev xs) x

rev-snoc : ∀ {ℓ} {A : Set ℓ} (l : List A) (x : A) → rev (snoc l x) ≡ x ∷ rev l
rev-snoc [] y = refl _
rev-snoc (x ∷ xs) y =
  snoc (rev (snoc xs y)) x  ≡⟨ cong (λ l → snoc l x) $ rev-snoc xs y ⟩∎
  y ∷ snoc (rev xs) x       ∎

rev-rev : ∀ {ℓ} {A : Set ℓ} (l : List A) → rev (rev l) ≡ l
rev-rev [] = refl _
rev-rev (x ∷ xs) =
  rev (snoc (rev xs) x) ≡⟨ rev-snoc (rev xs) x ⟩
  x ∷ rev (rev xs)      ≡⟨ cong (λ l → x ∷ l) $ rev-rev xs ⟩∎
  x ∷ xs                ∎

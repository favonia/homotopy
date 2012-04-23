------------------------------------------------------------------------
-- Lemmas for Fin
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

module Space.Fin.Lemmas where

open import Prelude
open import Path

decide-≡ : ∀ {n} (x : Fin n) (y : Fin n) → Dec (x ≡ y)
decide-≡ {zero} () ()
decide-≡ {suc _} (inj₁ tt) (inj₁ tt) = inj₁ $ refl _
decide-≡ {suc _} (inj₂ x) (inj₂ y) with decide-≡ x y
...                                | inj₁ eq  = inj₁ $ cong inj₂ eq
...                                | inj₂ neq = inj₂ $ neq ∘ cong λ{(inj₂ x) → x; (inj₁ _) → x}
decide-≡ {suc _} (inj₂ _) (inj₁ _) = inj₂ λ eq → subst (λ{(inj₂ _) → ⊤; (inj₁ _) → ⊥}) eq tt
decide-≡ {suc _} (inj₁ _) (inj₂ _) = inj₂ λ eq → subst (λ{(inj₁ _) → ⊤; (inj₂ _) → ⊥}) eq tt

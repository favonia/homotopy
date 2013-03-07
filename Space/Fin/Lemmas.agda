------------------------------------------------------------------------
-- Lemmas for Fin
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

module Space.Fin.Lemmas where

open import Prelude
open import Path

decide-≡ : ∀ {n} (x y : Fin n) → Dec (x ≡ y)
decide-≡ {zero} () ()
decide-≡ {suc _} (inj₁ tt) (inj₁ tt) = inj₁ $ refl _
decide-≡ {suc _} (inj₂ x) (inj₂ y) with decide-≡ x y
...                                | inj₁ eq  = inj₁ $ cong inj₂ eq
...                                | inj₂ neq = inj₂ $ neq ∘ cong λ{(inj₂ x) → x; (inj₁ _) → x}
decide-≡ {suc _} (inj₂ _) (inj₁ _) = inj₂ λ eq → subst (λ{(inj₂ _) → ⊤; (inj₁ _) → ⊥}) eq tt
decide-≡ {suc _} (inj₁ _) (inj₂ _) = inj₂ λ eq → subst (λ{(inj₁ _) → ⊤; (inj₂ _) → ⊥}) eq tt

data _<>_ : ∀ {n} (x y : Fin n) → Set where
  0<>s : ∀ {n} {x : Fin n} → inj₁ tt <> inj₂ x
  s<>0 : ∀ {n} {x : Fin n} → inj₂ x  <> inj₁ tt
  s<>s : ∀ {n} {x y : Fin n} → x <> y → inj₂ x <> inj₂ y

decide-≡' : ∀ {n} (x y : Fin n) → x ≡ y ⊎ x <> y
decide-≡' {zero} () ()
decide-≡' {suc _} (inj₁ tt) (inj₁ tt) = inj₁ $ refl _
decide-≡' {suc _} (inj₂ _) (inj₁ _) = inj₂ s<>0
decide-≡' {suc _} (inj₁ _) (inj₂ _) = inj₂ 0<>s
decide-≡' {suc _} (inj₂ x) (inj₂ y) with decide-≡' x y
...                                 | inj₁ eq  = inj₁ $ cong inj₂ eq
...                                 | inj₂ neq = inj₂ $ s<>s neq

<>-sym : ∀ {n} {x y : Fin n} → x <> y → y <> x
<>-sym 0<>s       = s<>0
<>-sym s<>0       = 0<>s
<>-sym (s<>s neq) = s<>s $ <>-sym neq

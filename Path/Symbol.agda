------------------------------------------------------------------------
-- Symbols for paths
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

module Path.Symbol where

open import Path

!_ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
!_ = sym

_◇_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_◇_ = trans

infixr 6 _◇_

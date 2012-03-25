------------------------------------------------------------------------
-- Spheres.
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

-- Currently we have S¹ and an experimental S²

{-# OPTIONS --without-K #-}

module Space.Interval where

open import Prelude hiding (zero)
open import Path
open import Path.Lemmas

------------------------------------------------------------------------
-- Formation rules and introduction rules

private
  data I′ : Set where
    zero′ : I′
    one′ : I′

I : Set
I = I′

zero : I
zero = zero′

one : I
one = one′

postulate
  seg : zero ≡ one

I-rec : ∀ {ℓ} (P : I → Set ℓ) (pzero : P zero) (pone : P one) → subst P seg pzero ≡ pone → (x : I) → P x
I-rec P pzero _ _ zero′ = pzero
I-rec P _ pone _ one′ = pone

postulate  
  I-rec-seg : ∀ {ℓ} (P : I → Set ℓ) (pzero : P zero) (pone : P one) (pseg : subst P seg pzero ≡ pone)
              → cong[dep] P (I-rec P pzero pone pseg) seg ≡ pseg

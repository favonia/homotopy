------------------------------------------------------------------------
-- Integers and their friends
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

module Inductive.Integer where

open import Prelude renaming (suc to ℕsuc; zero to ℕzero)

------------------------------------------------------------------------
-- Integers

-- Note that ⟦ pos n ⟧ = n + 1 and ⟦ neg n ⟧ = - (n + 1)

data ℤ : Set where
  pos : ℕ → ℤ
  neg : ℕ → ℤ
  zero : ℤ

-- An experimental ℤ that might be suitable for induction (??)
data ℤ″ : ℕ → Set where
  pos′ : (n : ℕ) → ℤ″ (ℕsuc n)
  neg′ : (n : ℕ) → ℤ″ (ℕsuc n)
  zero′ : ℤ″ ℕzero

ℤ′ : Set
ℤ′ = ∃ ℤ″

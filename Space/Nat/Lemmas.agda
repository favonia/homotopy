------------------------------------------------------------------------
-- Basic facts about natural numbers.
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

module Space.Nat.Lemmas where

open import Prelude
open import Path

n+0 : ∀ n → n + 0 ≡ n
n+0 0       = refl _
n+0 (suc n) = cong suc $ n+0 n

n+suc : ∀ n m → n + suc m ≡ suc n + m
n+suc 0       m = refl _
n+suc (suc n) m = cong suc $ n+suc n m

------------------------------------------------------------------------
-- Injections
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

module Injection where

open import Path
open import Path.Lemmas
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

------------------------------------------------------------------------
-- Injections

-- The property of being injective.

Injective : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

infix 0 _↣_

-- Injections.

record _↣_ {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    to        : From → To
    injective : Injective to

------------------------------------------------------------------------
-- Preorder

-- _↣_ is a preorder.

id : ∀ {a} {A : Set a} → A ↣ A
id = record
  { to        = P.id
  ; injective = P.id
  }

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      B ↣ C → A ↣ B → A ↣ C
f ∘ g = record
  { to        = to′
  ; injective = injective′
  }
  where
  open _↣_

  to′ = to f ⊚ to g

  abstract
    injective′ : Injective to′
    injective′ = injective g ⊚ injective f

-- "Equational" reasoning combinators.

infix  0 finally-↣
infixr 0 _↣⟨_⟩_

_↣⟨_⟩_ : ∀ {a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ↣ B → B ↣ C → A ↣ C
_ ↣⟨ A↣B ⟩ B↣C = B↣C ∘ A↣B

finally-↣ : ∀ {a b} (A : Set a) (B : Set b) → A ↣ B → A ↣ B
finally-↣ _ _ A↣B = A↣B

syntax finally-↣ A B A↣B = A ↣⟨ A↣B ⟩□ B □

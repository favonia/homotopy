------------------------------------------------------------------------
-- Equivalences
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

module Equivalence where

open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

------------------------------------------------------------------------
-- Equivalence

-- A ⇔ B means that A and B are equivalent.

infix 0 _⇔_

record _⇔_ {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    to   : From → To
    from : To → From

------------------------------------------------------------------------
-- Equivalence relation

-- _⇔_ is an equivalence relation.

id : ∀ {a} {A : Set a} → A ⇔ A
id = record
  { to   = P.id
  ; from = P.id
  }

inverse : ∀ {a b} {A : Set a} {B : Set b} → A ⇔ B → B ⇔ A
inverse A⇔B = record
  { to               = from
  ; from             = to
  } where open _⇔_ A⇔B

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      B ⇔ C → A ⇔ B → A ⇔ C
f ∘ g = record
  { to   = to   f ⊚ to   g
  ; from = from g ⊚ from f
  } where open _⇔_

-- "Equational" reasoning combinators.

infix  0 finally-⇔
infixr 0 _⇔⟨_⟩_

_⇔⟨_⟩_ : ∀ {a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ⇔ B → B ⇔ C → A ⇔ C
_ ⇔⟨ A⇔B ⟩ B⇔C = B⇔C ∘ A⇔B

finally-⇔ : ∀ {a b} (A : Set a) (B : Set b) → A ⇔ B → A ⇔ B
finally-⇔ _ _ A⇔B = A⇔B

syntax finally-⇔ A B A⇔B = A ⇔⟨ A⇔B ⟩□ B □

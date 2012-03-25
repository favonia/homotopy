------------------------------------------------------------------------
-- Surjections
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

module Map.Surjection where

open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
open import Path

open import Map.Equivalence as Equivalence
  using (_⇔_; module _⇔_) renaming (_∘_ to _⊙_)

------------------------------------------------------------------------
-- Surjections

infix 0 _↠_

-- Surjections.

record _↠_ {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    equivalence : From ⇔ To

  open _⇔_ equivalence

  field
    right-inverse-of : ∀ x → to (from x) ≡ x

  -- A lemma.

  from-to : ∀ {x y} → from x ≡ y → to y ≡ x
  from-to {x} {y} from-x≡y =
    to y         ≡⟨ cong to $ sym from-x≡y ⟩
    to (from x)  ≡⟨ right-inverse-of x ⟩∎
    x            ∎

  open _⇔_ equivalence public

------------------------------------------------------------------------
-- Preorder

-- _↠_ is a preorder.

id : ∀ {a} {A : Set a} → A ↠ A
id = record
  { equivalence      = Equivalence.id
  ; right-inverse-of = refl
  }

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      B ↠ C → A ↠ B → A ↠ C
f ∘ g = record
  { equivalence      = equivalence f ⊙ equivalence g
  ; right-inverse-of = to∘from
  }
  where
  open _↠_

  abstract
    to∘from : ∀ x → to f (to g (from g (from f x))) ≡ x
    to∘from = λ x →
      to f (to g (from g (from f x)))  ≡⟨ cong (to f) (right-inverse-of g (from f x)) ⟩
      to f (from f x)                  ≡⟨ right-inverse-of f x ⟩∎
      x                                ∎

-- "Equational" reasoning combinators.

infix  0 finally-↠
infixr 0 _↠⟨_⟩_

_↠⟨_⟩_ : ∀ {a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ↠ B → B ↠ C → A ↠ C
_ ↠⟨ A↠B ⟩ B↠C = B↠C ∘ A↠B

finally-↠ : ∀ {a b} (A : Set a) (B : Set b) → A ↠ B → A ↠ B
finally-↠ _ _ A↠B = A↠B

syntax finally-↠ A B A↠B = A ↠⟨ A↠B ⟩□ B □


------------------------------------------------------------------------
-- Bijections
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

module Bijection where

open import Path
open import Path.Lemmas
import Equivalence
open import Injection using (Injective; _↣_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
open import Surjection using (_↠_; module _↠_)

------------------------------------------------------------------------
-- Bijections

infix 0 _↔_

record _↔_ {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    surjection : From ↠ To

  open _↠_ surjection

  field
    left-inverse-of : ∀ x → from (to x) ≡ x

  injective : Injective to
  injective {x = x} {y = y} to-x≡to-y =
    x            ≡⟨ sym (left-inverse-of x) ⟩
    from (to x)  ≡⟨ cong from to-x≡to-y ⟩
    from (to y)  ≡⟨ left-inverse-of y ⟩∎
    y            ∎

  injection : From ↣ To
  injection = record
    { to        = to
    ; injective = injective
    }

  -- A lemma.

  to-from : ∀ {x y} → to x ≡ y → from y ≡ x
  to-from {x} {y} to-x≡y =
    from y       ≡⟨ cong from $ sym to-x≡y ⟩
    from (to x)  ≡⟨ left-inverse-of x ⟩∎
    x            ∎

  open _↠_ surjection public

------------------------------------------------------------------------
-- Equivalence

-- _↔_ is an equivalence relation.

id : ∀ {a} {A : Set a} → A ↔ A
id = record
  { surjection      = Surjection.id
  ; left-inverse-of = refl
  }

inverse : ∀ {a b} {A : Set a} {B : Set b} → A ↔ B → B ↔ A
inverse A↔B = record
  { surjection = record
    { equivalence      = Equivalence.inverse equivalence
    ; right-inverse-of = left-inverse-of
    }
  ; left-inverse-of = right-inverse-of
  } where open _↔_ A↔B

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      B ↔ C → A ↔ B → A ↔ C
f ∘ g = record
  { surjection      = Surjection._∘_ (surjection f) (surjection g)
  ; left-inverse-of = from∘to
  }
  where
  open _↔_

  abstract
    from∘to : ∀ x → from g (from f (to f (to g x))) ≡ x
    from∘to = λ x →
      from g (from f (to f (to g x)))  ≡⟨ cong (from g) (left-inverse-of f (to g x)) ⟩
      from g (to g x)                  ≡⟨ left-inverse-of g x ⟩∎
      x                                ∎

-- "Equational" reasoning combinators.

infix  0 finally-↔
infixr 0 _↔⟨_⟩_

_↔⟨_⟩_ : ∀ {a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ↔ B → B ↔ C → A ↔ C
_ ↔⟨ A↔B ⟩ B↔C = B↔C ∘ A↔B

finally-↔ : ∀ {a b} (A : Set a) (B : Set b) → A ↔ B → A ↔ B
finally-↔ _ _ A↔B = A↔B

syntax finally-↔ A B A↔B = A ↔⟨ A↔B ⟩□ B □

------------------------------------------------------------------------
-- Weak equivalences
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on univalent foundations.

module Map.WeakEquivalence where

open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
open import Path

open import Map.Surjection using (_↠_; module _↠_)
open import Map.H-equivalence as H-equiv hiding (id; _∘_; inverse)
open import Map.H-fiber as H-fiber

------------------------------------------------------------------------
-- Is-weak-equivalence

-- A function f is a weak equivalence if all h-fibers under f are
-- contractible.

Is-weak-equivalence : ∀ {a b} {A : Set a} {B : Set b} →
                      (A → B) → Set (a ⊔ b)
Is-weak-equivalence f = ∀ y → Contractible (f ⁻¹ y)

------------------------------------------------------------------------
-- _≈_

-- Weak equivalences.

infix 4 _≈_

record _≈_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor weq
  field
    to                  : A → B
    is-weak-equivalence : Is-weak-equivalence to

  -- Weakly equivalent sets are isomorphic.

  from : B → A
  from = proj₁ ⊚ proj₁ ⊚ is-weak-equivalence

  abstract
    right-inverse-of : ∀ x → to (from x) ≡ x
    right-inverse-of = proj₂ ⊚ proj₁ ⊚ is-weak-equivalence

    left-inverse-of : ∀ x → from (to x) ≡ x
    left-inverse-of  = λ x →
      cong (proj₁ {B = λ x′ → to x′ ≡ to x}) $
        proj₂ (is-weak-equivalence (to x)) (x , refl (to x))

  hequivalence : A ↔ B
  hequivalence = record
    { surjection = record
      { to               = to
      ; from             = from
      ; right-inverse-of = right-inverse-of
      }
    ; left-inverse-of = left-inverse-of
    }

  open _↔_ hequivalence public
    hiding (from; to; right-inverse-of; left-inverse-of)

  abstract

    -- All homotopy fibers of an element under the weak equivalence are
    -- equal.

    irrelevance : ∀ y (p : to ⁻¹ y) → (from y , right-inverse-of y) ≡ p
    irrelevance = proj₂ ⊚ is-weak-equivalence

    -- The two proofs left-inverse-of and right-inverse-of are
    -- related. (I.e., zigzag identity for adjoint equivalences.)

    left-right-lemma :
      ∀ x → cong to (left-inverse-of x) ≡ right-inverse-of (to x)
    left-right-lemma x =
      lemma₁ to (left-inverse-of x) _ (lemma₂ (irrelevance (to x) (x , refl (to x))))
      where
      lemma₁ : {x y : A} (f : A → B) (p : x ≡ y) (q : f x ≡ f y) →
               refl (f y) ≡ trans (cong f (sym p)) q →
               cong f p ≡ q
      lemma₁ f = elim
        (λ {x y} p → ∀ q → refl (f y) ≡ trans (cong f (sym p)) q →
                           cong f p ≡ q)
        (λ x q hyp →
           cong f (refl x)                  ≡⟨ refl _ ⟩
           refl (f x)                       ≡⟨ hyp ⟩∎
--         trans (cong f (sym (refl x))) q  ≡⟨ refl _ ⟩
--         trans (cong f (refl x)) q        ≡⟨ refl _ ⟩
--         trans (refl (f x)) q             ≡⟨ refl _ ⟩∎
           q                                ∎)

      lemma₂ : ∀ {f : A → B} {y} {f⁻¹y₁ f⁻¹y₂ : f ⁻¹ y}
               (p : f⁻¹y₁ ≡ f⁻¹y₂) →
               proj₂ f⁻¹y₂ ≡
               trans (cong f (sym (cong (proj₁ {B = λ x → f x ≡ y}) p)))
                     (proj₂ f⁻¹y₁)
      lemma₂ {f} {y} =
        let pr = proj₁ {B = λ x → f x ≡ y} in
        elim {A = f ⁻¹ y}
          (λ {f⁻¹y₁ f⁻¹y₂} p →
             proj₂ f⁻¹y₂ ≡
               trans (cong f (sym (cong pr p))) (proj₂ f⁻¹y₁))
          (λ f⁻¹y →
             proj₂ f⁻¹y                                               ≡⟨ refl _ ⟩
             trans (refl (f (proj₁ f⁻¹y))) (proj₂ f⁻¹y)               ≡⟨ refl _ ⟩
             trans (cong f (refl (proj₁ f⁻¹y))) (proj₂ f⁻¹y)          ≡⟨ refl _ ⟩
             trans (cong f (sym (refl (proj₁ f⁻¹y)))) (proj₂ f⁻¹y)    ≡⟨ refl _ ⟩∎
             trans (cong f (sym (cong pr (refl f⁻¹y)))) (proj₂ f⁻¹y)  ∎)

-- Homotopy equivalences are weak equivalences.

↔⇒≈ : ∀ {a b} {A : Set a} {B : Set b} → A ↔ B → A ≈ B
↔⇒≈ A↔B = record
  { to                  = _↔_.to A↔B
  ; is-weak-equivalence = H-fiber.hequiv⁻¹-contractible A↔B
  }

------------------------------------------------------------------------
-- Equivalence

-- Weak equivalences are equivalence relations.

-- This is subject to changes
id : ∀ {a} {A : Set a} → A ≈ A
-- id = ↔⇒≈ H-equiv.id
id = record
  { to                  = P.id
  ; is-weak-equivalence = H-fiber.id⁻¹-contractible
  }

inverse : ∀ {a b} {A : Set a} {B : Set b} → A ≈ B → B ≈ A
inverse = ↔⇒≈ ⊚ H-equiv.inverse ⊚ _≈_.hequivalence

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      B ≈ C → A ≈ B → A ≈ C
f ∘ g = ↔⇒≈ $ H-equiv._∘_ (_≈_.hequivalence f) (_≈_.hequivalence g)

-- Equational reasoning combinators.

infixr 0 _≈⟨_⟩_
infix  0 finally-≈

_≈⟨_⟩_ : ∀ {a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ≈ B → B ≈ C → A ≈ C
_ ≈⟨ A≈B ⟩ B≈C = B≈C ∘ A≈B

finally-≈ : ∀ {a b} (A : Set a) (B : Set b) → A ≈ B → A ≈ B
finally-≈ _ _ A≈B = A≈B

syntax finally-≈ A B A≈B = A ≈⟨ A≈B ⟩□ B □

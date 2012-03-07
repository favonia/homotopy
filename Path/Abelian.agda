------------------------------------------------------------------------
-- Ω₂(A) is abelian
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

-- Ω₂(A) for any type A is abelian.

-- Credits:
--
--  * The long (unfinished) proof is from
--    (1) Dan Licata's post
--        http://homotopytypetheory.org/2011/03/26/higher-fundamental-groups-are-abelian/
--    (2) Wikipedia on the Eckmann-Hilton argument
--        http://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument
--
--  * I found a much shorter proof while following the above approach.

module Path.Abelian {ℓ} {A : Set ℓ} (base : A) where
 
open import Prelude hiding (_∘_)
open import Path
open import Path.Lemmas

private
  Ω₁A = base ≡ base
  Ω₂A = refl base ≡ refl base

  lemma₁ : ∀ (p : Ω₂A) → cong (λ p′ → trans p′ (refl base)) p ≡ p
  lemma₁ p = elim″ (λ {x} p → cong (λ p → trans p (refl _)) p ≡ trans (trans-reflʳ x) p) (refl _) p

  lemma₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
           (f : A → B → C) {x y : A} {u v : B}
           (p : x ≡ y) (q : u ≡ v) → cong₂ f p q ≡ cong₂′ f p q
  lemma₂ f p q = elim (λ {_ _} p → cong₂ f p q ≡ cong₂′ f p q) (λ _ → sym $ trans-reflʳ _) p

abelian : ∀ (p q : Ω₂A) → trans p q ≡ trans q p
abelian p q =
  trans p q                                                 ≡⟨ cong (trans p) $ sym $ cong-id q ⟩
  trans p (cong id q)                                       ≡⟨ cong (flip trans (cong id q)) $ sym $ lemma₁ p ⟩
  trans (cong (λ p′ → trans p′ (refl base)) p) (cong id q)  ≡⟨ lemma₂ trans p q ⟩
  trans (cong id q) (cong (λ p′ → trans p′ (refl base)) p)  ≡⟨ cong (trans (cong id q)) $ lemma₁ p ⟩
  trans (cong id q) p                                       ≡⟨ cong (flip trans p) $ cong-id q ⟩∎
  trans q p                                                 ∎

------------------------------------------------------------------------
-- The following are way too complex for the abelianess theorem,
-- but might be useful in the future.

private
  record IsUnital {ℓ} (A : Set ℓ) (_∘_ : A → A → A) (unit : A) : Set ℓ where
    field
      unitʳ : ∀ (x : A) → x ∘ unit ≡ x
      unitˡ : ∀ (x : A) → unit ∘ x ≡ x
      -- Monoid is unnecessary. Unital is enough.
      -- assoc : ∀ (x y z : A) → (x ∘ y) ∘ z ≡ x ∘ (y ∘ z)

  module EckmannHilton {ℓ}
    {A : Set ℓ} {_∘_ : A → A → A} {_∙_ : A → A → A} {unit : A}
    (M₁′ : IsUnital A _∘_ unit) (M₂′ : IsUnital A _∙_ unit)
    (interchange : ∀ (x y z w : A) → (x ∙ y) ∘ (z ∙ w) ≡ (x ∘ z) ∙ (y ∘ w)) where

    private
      module M₁ where
        open IsUnital M₁′ public
      module M₂ where
        open IsUnital M₂′ public

    same : ∀ (x y : A) → x ∘ y ≡ x ∙ y
    same x y =
      x ∘ y                   ≡⟨ cong (λ z → z ∘ y) $ sym $ M₂.unitʳ x ⟩
      (x ∙ unit) ∘ y          ≡⟨ cong (λ z → (x ∙ unit) ∘ z) $ sym $ M₂.unitˡ y ⟩
      (x ∙ unit) ∘ (unit ∙ y) ≡⟨ interchange x unit unit y ⟩
      (x ∘ unit) ∙ (unit ∘ y) ≡⟨ cong (λ z → z ∙ (unit ∘ y)) $ M₁.unitʳ x ⟩
      x ∙ (unit ∘ y)          ≡⟨ cong (λ z → x ∙ z) $ M₁.unitˡ y ⟩∎
      x ∙ y                   ∎

    abelian′ : ∀ (x y : A) → x ∘ y ≡ y ∘ x
    abelian′ x y =
      x ∘ y                   ≡⟨ same x y ⟩
      x ∙ y                   ≡⟨ cong (λ z → z ∙ y) $ sym $ M₁.unitˡ x ⟩
      (unit ∘ x) ∙ y          ≡⟨ cong (λ z → (unit ∘ x) ∙ z) $ sym $ M₁.unitʳ y ⟩
      (unit ∘ x) ∙ (y ∘ unit) ≡⟨ sym $ interchange unit y x unit ⟩
      (unit ∙ y) ∘ (x ∙ unit) ≡⟨ cong (λ z → (unit ∙ y) ∘ z) $ M₂.unitʳ x ⟩
      (unit ∙ y) ∘ x          ≡⟨ cong (λ z → z ∘ x) $ M₂.unitˡ y ⟩∎
      y ∘ x                   ∎

  _∘_ : ∀ {ℓ} {B : Set ℓ} {x y z : B} → x ≡ y → y ≡ z → x ≡ z
  _∘_ = trans
  _∙_ : ∀ {x y z w : base ≡ base} → x ≡ y → z ≡ w → trans x z ≡ trans y w
  _∙_ = cong₂ trans
  unit = refl (refl base)

  trans-unital : IsUnital Ω₂A _∘_ unit
  trans-unital = record
    { unitʳ = trans-reflʳ
    ; unitˡ = λ _ → refl _
    --; assoc = trans-assoc
    }

  cong₂-trans-unital : IsUnital Ω₂A _∙_ unit
  cong₂-trans-unital = record
    { unitʳ = unitʳ
    ; unitˡ = unitˡ
    --; assoc = assoc
    } where
      unitʳ : ∀ p → p ∙ unit ≡ p
      unitʳ p = elim″ (λ {x} p → p ∙ unit ≡ (trans-reflʳ x) ∘ p) (refl _) p

      unitˡ : ∀ p → unit ∙ p ≡ p
      unitˡ p = elim″ (λ {_} p → unit ∙ p ≡ p) (refl _) p
      {-
      assoc : ∀ p q r → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
      assoc p q r = elim″
        (λ {x} p → (p ∙ q) ∙ r ≡ trans-assoc x (refl base) (refl base) ∘ (p ∙ (q ∙ r)))
        ((unit ∙ q) ∙ r ≡⟨ cong (λ pq → pq ∙ r) $ unitˡ q ⟩
         q ∙ r          ≡⟨ sym $ unitˡ (q ∙ r) ⟩∎
         unit ∙ (q ∙ r) ∎)
        p
      -}

  -- The effort to prove this is more than enough to prove abelianness:
  -- interchange : ∀ (x y z w : Ω₂A) → (x ∙ y) ∘ (z ∙ w) ≡ (x ∘ z) ∙ (y ∘ w)

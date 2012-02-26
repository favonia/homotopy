------------------------------------------------------------------------
-- More lemmas
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Prelude
open import Equality
import Univalence-axiom

module Univalence.Misc
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive)
  (univ : ∀ {ℓ} (A : Set ℓ) (B : Set ℓ) → Univalence-axiom.Univalence-axiom′ eq A B) where

open Derived-definitions-and-properties eq
import Equality.Misc; open Equality.Misc eq

open Univalence-axiom eq
private
  module Bijection where
    import Bijection; open Bijection eq public
open Bijection hiding (_∘_; id)
private
  module Weak where
    import Weak-equivalence; open Weak-equivalence eq public
open Weak hiding (_∘_; id)

------------------------------------------------------------------------
-- Conversions between bijections, weak equivalences, and identities

≈⇒≡ : ∀ {ℓ} {A B : Set ℓ} → A ≈ B → A ≡ B
≈⇒≡ = _≈_.from (≡≈≈ (univ _ _))

↔⇒≈ : ∀ {ℓ} {A B : Set ℓ} → A ↔ B → A ≈ B
↔⇒≈ = bijection⇒weak-equivalence

↔⇒≡ : ∀ {ℓ} {A B : Set ℓ} → A ↔ B → A ≡ B
↔⇒≡ = ≈⇒≡ ∘ ↔⇒≈

≡⇒≈-refl : ∀ {ℓ} {A : Set ℓ} → (≡⇒≈ (refl A)) ≡ Weak.id
≡⇒≈-refl = elim-refl (λ {A B} _ → A ≈ B) (λ _ → Weak.id)

subst-id-≡ : ∀ {ℓ} {A B : Set ℓ} (A≡B : A ≡ B) (x : A) → subst id A≡B x ≡ _≈_.to (≡⇒≈ A≡B) x 
subst-id-≡ {ℓ} =
  elim
    (λ {A B : Set ℓ} (A≡B : A ≡ B) → (x : A) → subst id A≡B x ≡ _≈_.to (≡⇒≈ A≡B) x)
    (λ A x → 
       subst id (refl A) x          ≡⟨ subst-refl id x ⟩
       x                            ≡⟨ refl x ⟩
       (_≈_.to Weak.id) x           ≡⟨ cong (λ weq → (_≈_.to weq) x) $ sym $ ≡⇒≈-refl ⟩∎
       (_≈_.to (≡⇒≈ (refl A))) x    ∎)

univ-left-inverse-of : ∀ {ℓ} {A B : Set ℓ} (A≡B : A ≡ B) → (≈⇒≡ (≡⇒≈ A≡B)) ≡ A≡B
univ-left-inverse-of A≡B = _≈_.left-inverse-of (≡≈≈ (univ _ _)) A≡B

univ-right-inverse-of : ∀ {ℓ} {A B : Set ℓ} (A≈B : A ≈ B) → (≡⇒≈ (≈⇒≡ A≈B)) ≡ A≈B
univ-right-inverse-of A≈B = _≈_.right-inverse-of (≡≈≈ (univ _ _)) A≈B

extensionality′ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
extensionality′ {B = B} = extensionality (univ (B ²/≡) B)

------------------------------------------------------------------------
-- TODO
{-
cong-extensionality′ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f g : A → B} (x→fx≡gx : ∀ x → f x ≡ g x) → f ≡ g →
                          ∀ (x : A) → cong (λ f → f x) (extensionality′ x→fx≡gx) ≡ x→fx≡gx x
-}

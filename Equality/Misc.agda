------------------------------------------------------------------------
-- More lemmas for equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- This should be viewed as an extension to Equality.Tactic

open import Prelude
open import Equality

module Equality.Misc
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where
 
open Derived-definitions-and-properties eq
open Equality-with-substitutivity-and-contractibility′ (J⇒subst+contr eq) using (trans-sym) -- reuse the proof
import Equality.Tactic; open Equality.Tactic eq

{-

-- Stuffs from Equality.Tactic

trans-reflʳ p : trans p (refl y) ≡ p

trans-reflˡ p : trans (refl x) p ≡ p

sym-sym p : sym (sym p) ≡ p

sym-trans p q : sym (trans p q) ≡ trans (sym p) (sym q)

-- should be reversed
cong-id p : p ≡ cong id p

-- should be reversed
cong-∘ f g p : cong f (cong g x≡y) ≡ cong (f ∘ g) x≡y

cong-sym f p : cong f (sym p) ≡ sym (cong f p)

cong-trans f p q : cong f (trans p q) ≡ trans (cong f p) (cong f q)

trans-assoc p q r : trans (trans p q) r ≡ trans p (trans q r)

-}

-- Derived² lemmas

trans-symˡ : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
              trans (sym x≡y) x≡y ≡ refl y
trans-symˡ = trans-sym

trans-symʳ : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
              trans x≡y (sym x≡y) ≡ refl x
trans-symʳ =
  elim
    (λ {x y} p → trans p (sym p) ≡ refl x)
    (λ x →
      trans (refl x) (sym (refl x))   ≡⟨ cong (trans (refl x)) $ sym-refl ⟩
      trans (refl x) (refl x)         ≡⟨ trans-refl-refl ⟩∎
      refl x                          ∎)

cong-cong : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {x y : A}
            (f : B → C) (g : A → B) (p : x ≡ y) →
            cong f (cong g p) ≡ cong (f ∘ g) p
cong-cong = cong-∘

cong-id′ : ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) →
           cong id p ≡ p
cong-id′ p = sym $ cong-id p

cong[dep] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) (f : (x : A) → B x)
            {x y : A} (p : x ≡ y) → subst B p (f x) ≡ (f y)
cong[dep] B f =
  elim
    (λ {x y} p → subst B p (f x) ≡ (f y) )
    (λ x → subst-refl B (f x))

abstract
  cong[dep]-refl : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) (f : (x : A) → B x) {x : A} →
                   cong[dep] B f (refl x) ≡ subst-refl B (f x)
  cong[dep]-refl B f {x} =
    elim-refl
      (λ {x y} p → subst B p (f x) ≡ (f y) )
      (λ x → subst-refl B (f x))

cong-const : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (b : B) {x y : A} (p : x ≡ y) → cong (const b) p ≡ refl b
cong-const {B = B} b p =
  elim
    (λ {_ _} p → cong (const b) p ≡ refl b )
    (λ x → cong-refl (const b))
    p

subst-trans : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {x y : A}
              (p₁ : x ≡ y) {z : A} (p₂ : y ≡ z) (b : B x) →
              subst B (trans p₁ p₂) b ≡ subst B p₂ (subst B p₁ b)
subst-trans {A = A} B =
  elim
    (λ {x y} p₁ → {z : A} (p₂ : y ≡ z) (b : B x) →
        subst B (trans p₁ p₂) b ≡ subst B p₂ (subst B p₁ b))
    (λ x p₂ b →
        subst B (trans (refl _) p₂) b   ≡⟨ cong (λ p → subst B p b) (trans-reflˡ p₂) ⟩
        subst B p₂ b                    ≡⟨ cong (subst B p₂) $ sym $ subst-refl B b ⟩∎
        subst B p₂ (subst B (refl _) b) ∎)

subst-sym : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂}
            {x y : A} {p : x ≡ y} {bx : B x} {by : B y} →
            subst B p bx ≡ by → subst B (sym p) by ≡ bx
subst-sym {A = A} {B} {x} {y} {p} {bx} {by} proof =
    subst B (sym p) by              ≡⟨ cong (subst B (sym p)) $ sym proof ⟩
    subst B (sym p) (subst B p bx)  ≡⟨ sym $ subst-trans B p (sym p) bx ⟩
    subst B (trans p (sym p)) bx    ≡⟨ cong (λ p → subst B p bx) $ trans-symʳ p ⟩
    subst B (refl _) bx             ≡⟨ subst-refl B bx ⟩∎
    bx                              ∎

subst-const : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {x y : A} (p : x ≡ y) (b : B) → subst (const B) p b ≡ b
subst-const {B = B} p b =
  elim
    (λ {_ _} p → subst (const B) p b ≡ b )
    (λ x → subst-refl (const B) {x} b)
    p

abstract
  subst-const-refl : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {x : A} (b : B) → subst-const (refl x) b ≡ subst-refl (const B) {x} b
  subst-const-refl {B = B} {x} b =
    elim-refl
      (λ {_ _} p → subst (const B) p b ≡ b )
      (λ x → subst-refl (const B) {x} b)

subst-id-cong : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂)
             {x y : A} (p : x ≡ y) (b : B x) →
             subst id (cong B p) b ≡ subst B p b
subst-id-cong B =
  elim
    (λ {x y} p → (b : B x) → subst id (cong B p) b ≡ subst B p b)
    (λ x b →
        subst id (cong B (refl x)) b   ≡⟨ cong (λ p → subst id p b) (cong-refl B) ⟩
        subst id (refl (B x)) b        ≡⟨ subst-refl id b ⟩
        b                              ≡⟨ sym $ subst-refl B b ⟩∎
        subst B (refl _) b ∎)

subst-cong : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} (C : B → Set ℓ₃)
             (f : (x : A) → B) {x y : A} (p : x ≡ y) (c : C (f x)) →
             subst C (cong f p) c ≡ subst (C ∘ f) p c
subst-cong C f =
  elim
    (λ {x y} p → (c : C (f x)) → subst C (cong f p) c ≡ subst (C ∘ f) p c )
    (λ x c →
        subst C (cong f (refl _)) c   ≡⟨ cong (λ p → subst C p c) $ cong-refl f ⟩
        subst C (refl _) c            ≡⟨ subst-refl C c ⟩
        c                             ≡⟨ sym $ subst-refl (C ∘ f) c ⟩∎
        subst (C ∘ f) (refl _) c      ∎)

abstract
  subst-cong-refl : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} (C : B → Set ℓ₃)
                 (f : (x : A) → B) {x} (c : C (f x)) →
                 subst-cong C f (refl x) c ≡
                  (
                    subst C (cong f (refl _)) c   ≡⟨ cong (λ p → subst C p c) $ cong-refl f ⟩
                    subst C (refl _) c            ≡⟨ subst-refl C c ⟩
                    c                             ≡⟨ sym $ subst-refl (C ∘ f) c ⟩∎
                    subst (C ∘ f) (refl _) c      ∎)
  subst-cong-refl C f c = cong (λ f → f c) $
    elim-refl
      (λ {x y} p → (c : C (f x)) → subst C (cong f p) c ≡ subst (C ∘ f) p c )
      (λ x c →
        subst C (cong f (refl _)) c   ≡⟨ cong (λ p → subst C p c) $ cong-refl f ⟩
        subst C (refl _) c            ≡⟨ subst-refl C c ⟩
        c                             ≡⟨ sym $ subst-refl (C ∘ f) c ⟩∎
        subst (C ∘ f) (refl _) c      ∎)

subst-func : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} (B : A → Set ℓ₂) (C : A → Set ℓ₃) 
             {x y : A} (p : x ≡ y) →
             ∀ (f : B x → C x) (b : B y) →
             subst (λ x → B x → C x) p f b ≡ (subst C p $ f $ subst B (sym p) b)
subst-func B C =
  elim
    (λ {x y} p → (f : B x → C x) (b : B y) →
        subst (λ x → B x → C x) p f b ≡ (subst C p $ f $ subst B (sym p) b))
    (λ x f b →
        subst (λ x → B x → C x) (refl _) f b              ≡⟨ cong (λ f → f b) $ subst-refl (λ x → B x → C x) f ⟩
        f b                                               ≡⟨ cong (λ b → f b) $ sym $ subst-refl B b ⟩
        f (subst B (refl _) b)                            ≡⟨ cong (λ p → f $ subst B p b) $ sym $ sym-refl ⟩
        f (subst B (sym (refl _)) b)                      ≡⟨ sym $ subst-refl C _ ⟩∎
        subst C (refl _) (f (subst B (sym (refl _)) b))   ∎)

subst-path[simp] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f g : A → B)
              {x y : A} (p : x ≡ y) (q : f x ≡ g x) →
              subst (λ x → f x ≡ g x) p q ≡ trans (sym (cong f p)) (trans q (cong g p))
subst-path[simp] f g =
  elim
    (λ {x y} (p : x ≡ y) → (q : f x ≡ g x) →
        subst (λ x → f x ≡ g x) p q ≡ trans (sym (cong f p)) (trans q (cong g p)))
    (λ x q →
        subst (λ x → f x ≡ g x) (refl _) q                        ≡⟨ subst-refl (λ x → f x ≡ g x) q ⟩
        q                                                         ≡⟨ sym $ trans-reflʳ q ⟩
        (trans q (refl _))                                        ≡⟨ sym $ trans-reflˡ _ ⟩
        trans (refl _) (trans q (refl _))                         ≡⟨ cong (λ p → trans p (trans q (refl _))) $ sym $ sym-refl ⟩
        trans (sym (refl _)) (trans q (refl _))                   ≡⟨ cong (λ p → trans (sym p) (trans q (refl _))) $ sym $ cong-refl f ⟩
        trans (sym (cong f (refl _))) (trans q (refl _))          ≡⟨ cong (λ p → trans (sym (cong f (refl _))) (trans q p)) $ sym $ cong-refl g ⟩∎
        trans (sym (cong f (refl _))) (trans q (cong g (refl _))) ∎)

-- Derived³ lemmas

cong[dep]-nondep : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B)
                  {x y : A} (p : x ≡ y) → cong[dep] (const B) f p ≡ (trans (subst-const p (f x)) (cong f p))
cong[dep]-nondep {B = B} f =
  elim
    (λ {x y} p → cong[dep] (const B) f p ≡ (trans (subst-const p (f x)) (cong f p)) )
    (λ x →
        cong[dep] (const B) f (refl x)                      ≡⟨ cong[dep]-refl (const B) f ⟩
        subst-refl (const B) (f x)                          ≡⟨ sym $ subst-const-refl (f x) ⟩
        subst-const (refl _) (f x)                          ≡⟨ sym $ trans-reflʳ _ ⟩
        trans (subst-const (refl _) (f x)) (refl _)         ≡⟨ cong (trans (subst-const (refl _) (f x))) $ sym $ cong-refl f ⟩∎
        trans (subst-const (refl _) (f x)) (cong f (refl _))∎)

trans-sym-trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} (p : y ≡ x) (q : x ≡ z) → trans (sym p) (trans p q) ≡ q
trans-sym-trans p q =
    trans (sym p) (trans p q)               ≡⟨ sym $ trans-assoc _ _ _ ⟩
    trans (trans (sym p) p) q               ≡⟨ cong (λ p → trans p q) $ trans-symˡ p ⟩
    trans (refl _) q                        ≡⟨ trans-reflˡ _ ⟩∎
    q                                       ∎

trans-transʳ-sym : ∀ {ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → trans p (trans (sym p) q) ≡ q
trans-transʳ-sym p q =
    trans p (trans (sym p) q)               ≡⟨ sym $ trans-assoc _ _ _ ⟩
    trans (trans p (sym p)) q               ≡⟨ cong (λ p → trans p q) $ trans-symʳ p ⟩
    trans (refl _) q                        ≡⟨ trans-reflˡ _ ⟩∎
    q                                       ∎

trans-trans-symʳ : ∀ {ℓ} {A : Set ℓ} {x y z : A} (q : x ≡ y) (p : z ≡ y) → trans (trans q (sym p)) p ≡ q
trans-trans-symʳ q p =
    trans (trans q (sym p)) p               ≡⟨ trans-assoc _ _ _ ⟩
    trans q (trans (sym p) p)               ≡⟨ cong (trans q) $ trans-symˡ p ⟩
    trans q (refl _)                        ≡⟨ trans-reflʳ _ ⟩∎
    q                                       ∎

trans-trans-symʳʳ : ∀ {ℓ} {A : Set ℓ} {x y z : A} (q : x ≡ y) (p : y ≡ z) → trans (trans q p) (sym p) ≡ q
trans-trans-symʳʳ q p =
    trans (trans q p) (sym p)               ≡⟨ trans-assoc _ _ _ ⟩
    trans q (trans p (sym p))               ≡⟨ cong (trans q) $ trans-symʳ p ⟩
    trans q (refl _)                        ≡⟨ trans-reflʳ _ ⟩∎
    q                                       ∎

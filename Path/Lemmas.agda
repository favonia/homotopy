------------------------------------------------------------------------
-- Lemmas for equality
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

open import Prelude
open import Path

module Path.Lemmas where

------------------------------------------------------------------------
-- Tons of lemmas

trans-reflʳ : ∀ {ℓ} {A : Set ℓ} {x y : A} (x≡y : x ≡ y) →
              trans x≡y (refl y) ≡ x≡y
trans-reflʳ =
  elim
    (λ {x y} x≡y → trans x≡y (refl y) ≡ x≡y)
    (λ x → refl _)

{-
trans-reflˡ : ∀ {ℓ} {A : Set ℓ} {x y : A} (x≡y : x ≡ y) →
              trans (refl x) x≡y ≡ x≡y
trans-reflˡ _ = refl _
-}

sym-sym : ∀ {ℓ} {A : Set ℓ} {x y : A} (x≡y : x ≡ y) →
          sym (sym x≡y) ≡ x≡y
sym-sym = elim (λ {u v} u≡v → sym (sym u≡v) ≡ u≡v)
               (λ x → refl _)

sym-trans : ∀ {a} {A : Set a} {x y z : A}
            (x≡y : x ≡ y) (y≡z : y ≡ z) →
            sym (trans x≡y y≡z) ≡ trans (sym y≡z) (sym x≡y)
sym-trans {a} =
  elim (λ x≡y → ∀ y≡z → sym (trans x≡y y≡z) ≡ trans (sym y≡z) (sym x≡y))
       (λ y y≡z → sym (trans (refl y) y≡z)        ≡⟨ refl _ ⟩
                  sym y≡z                         ≡⟨ sym $ trans-reflʳ _ ⟩∎
--                trans (sym y≡z) (refl y)        ≡⟨ refl _ ⟩∎
                  trans (sym y≡z) (sym (refl y))  ∎)

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        (f : A → B → C) {x y : A} {u v : B} →
        x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f {x} {y} {u} {v} x≡y u≡v =
  f x u  ≡⟨ cong (flip f u) x≡y ⟩
  f y u  ≡⟨ cong (f y)      u≡v ⟩∎
  f y v  ∎

cong-id : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
          cong id x≡y ≡ x≡y
cong-id = elim (λ {x y} x≡y → cong id x≡y ≡ x≡y)
               (λ x → cong id (refl x)  ≡⟨ refl _ ⟩∎
                      refl x            ∎)

cong-cong : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {x y : A}
            (f : B → C) (g : A → B) (x≡y : x ≡ y) →
            cong f (cong g x≡y) ≡ cong (f ∘ g) x≡y
cong-cong f g =
  elim
    (λ x≡y → cong f (cong g x≡y) ≡ cong (f ∘ g) x≡y)
    (λ x → refl _)

cong-sym : ∀ {a b} {A : Set a} {B : Set b} {x y : A}
           (f : A → B) (x≡y : x ≡ y) →
           cong f (sym x≡y) ≡ sym (cong f x≡y)
cong-sym f = elim (λ x≡y → cong f (sym x≡y) ≡ sym (cong f x≡y))
                  (λ x → refl _)

cong-trans : ∀ {a b} {A : Set a} {B : Set b} {x y z : A}
             (f : A → B) (x≡y : x ≡ y) (y≡z : y ≡ z) →
             cong f (trans x≡y y≡z) ≡ trans (cong f x≡y) (cong f y≡z)
cong-trans f =
  elim (λ x≡y → ∀ y≡z → cong f (trans x≡y y≡z) ≡
                        trans (cong f x≡y) (cong f y≡z))
       (λ y y≡z → cong f (trans (refl y) y≡z)           ≡⟨ refl _ ⟩∎
--                cong f y≡z                            ≡⟨ refl _ ⟩
--                trans (refl (f y)) (cong f y≡z)       ≡⟨ refl _ ⟩∎
                  trans (cong f (refl y)) (cong f y≡z)  ∎)


trans-assoc : ∀ {a} {A : Set a} {x y z u : A}
              (x≡y : x ≡ y) (y≡z : y ≡ z) (z≡u : z ≡ u) →
              trans (trans x≡y y≡z) z≡u ≡ trans x≡y (trans y≡z z≡u)
trans-assoc =
  elim (λ x≡y → ∀ y≡z z≡u → trans (trans x≡y y≡z) z≡u ≡
                            trans x≡y (trans y≡z z≡u))
       (λ y y≡z z≡u →
          trans (trans (refl y) y≡z) z≡u ≡⟨ refl _ ⟩∎
--        trans y≡z z≡u                  ≡⟨ refl _ ⟩∎
          trans (refl y) (trans y≡z z≡u) ∎)

-- Derived² lemmas

trans-symˡ : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
              trans (sym x≡y) x≡y ≡ refl y
trans-symˡ =
  elim
    (λ {x y} (x≡y : x ≡ y) → trans (sym x≡y) x≡y ≡ refl y)
    (λ x → trans (sym (refl x)) (refl x)  ≡⟨ refl _ ⟩∎
--         trans (refl x) (refl x)        ≡⟨ refl _ ⟩∎
           refl x                         ∎)

trans-symʳ : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
              trans x≡y (sym x≡y) ≡ refl x
trans-symʳ =
  elim
    (λ {x y} p → trans p (sym p) ≡ refl x)
    (λ x →
      trans (refl x) (sym (refl x))   ≡⟨ refl _ ⟩∎
--    trans (refl x) (refl x)         ≡⟨ refl _ ⟩∎
      refl x                          ∎)

cong[dep] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) (f : (x : A) → B x)
            {x y : A} (p : x ≡ y) → subst B p (f x) ≡ (f y)
cong[dep] B f =
  elim
    (λ {x y} p → subst B p (f x) ≡ (f y) )
    (λ x → refl _)

cong[dep]₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} (B : A → Set ℓ₂) (C : A → Set ℓ₃)
             (f : (x : A) → B x → C x) {a₁ a₂ : A} (p : a₁ ≡ a₂) {b₁ : B a₁} {b₂ : B a₂} (q : subst B p b₁ ≡ b₂) →
             subst C p (f a₁ b₁) ≡ f a₂ b₂
cong[dep]₂ B C f =
  elim
    (λ {a₁ a₂} p → {b₁ : B a₁} {b₂ : B a₂} (q : subst B p b₁ ≡ b₂) → subst C p (f a₁ b₁) ≡ f a₂ b₂)
    (λ a q → cong (f a) q)

cong-const : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (b : B) {x y : A} (p : x ≡ y) → cong (const b) p ≡ refl b
cong-const {B = B} b p =
  elim
    (λ {_ _} p → cong (const b) p ≡ refl b )
    (λ x → refl _)
    p

subst-trans : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {x y : A}
              (p₁ : x ≡ y) {z : A} (p₂ : y ≡ z) (b : B x) →
              subst B (trans p₁ p₂) b ≡ subst B p₂ (subst B p₁ b)
subst-trans {A = A} B =
  elim
    (λ {x y} p₁ → {z : A} (p₂ : y ≡ z) (b : B x) →
        subst B (trans p₁ p₂) b ≡ subst B p₂ (subst B p₁ b))
    (λ x p₂ b →
        subst B (trans (refl _) p₂) b   ≡⟨ refl _ ⟩∎
--      subst B p₂ b                    ≡⟨ refl _ ⟩∎
        subst B p₂ (subst B (refl _) b) ∎)


subst-sym : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂)
            {x y : A} (p : x ≡ y) (by : B y) (bx : B x) →
            subst B p bx ≡ by → subst B (sym p) by ≡ bx
subst-sym {A = A} B {x} {y} p by bx q =
    subst B (sym p) by              ≡⟨ cong (subst B (sym p)) $ sym q ⟩
    subst B (sym p) (subst B p bx)  ≡⟨ sym $ subst-trans B p (sym p) bx ⟩
    subst B (trans p (sym p)) bx    ≡⟨ cong (λ p → subst B p bx) $ trans-symʳ p ⟩∎
--  subst B (refl _) bx             ≡⟨ refl _ ⟩∎
    bx                              ∎

subst-const : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {x y : A} (p : x ≡ y) (b : B) → subst (const B) p b ≡ b
subst-const {B = B} p b =
  elim
    (λ {_ _} p → subst (const B) p b ≡ b )
    (λ x → refl _)
    p

subst-id-cong : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂)
             {x y : A} (p : x ≡ y) (b : B x) →
             subst id (cong B p) b ≡ subst B p b
subst-id-cong B =
  elim
    (λ {x y} p → (b : B x) → subst id (cong B p) b ≡ subst B p b)
    (λ x b →
        subst id (cong B (refl x)) b   ≡⟨ refl _ ⟩∎
--      subst id (refl (B x)) b        ≡⟨ refl _ ⟩
--      b                              ≡⟨ refl _ ⟩∎
        subst B (refl _) b ∎)

subst-cong : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} (C : B → Set ℓ₃)
             (f : (x : A) → B) {x y : A} (p : x ≡ y) (c : C (f x)) →
             subst C (cong f p) c ≡ subst (C ∘ f) p c
subst-cong C f =
  elim
    (λ {x y} p → (c : C (f x)) → subst C (cong f p) c ≡ subst (C ∘ f) p c )
    (λ x c →
        subst C (cong f (refl _)) c   ≡⟨ refl _ ⟩∎
--      subst C (refl _) c            ≡⟨ refl _ ⟩
--      c                             ≡⟨ refl _ ⟩∎
        subst (C ∘ f) (refl _) c      ∎)

subst-app : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} (B : A → Set ℓ₂) (C : A → Set ℓ₃)
            {x y : A} (p : x ≡ y) (f : B x → C x) {bx : B x} {by : B y} (q : subst B p bx ≡ by) →
            subst C p (f bx) ≡ (subst (λ x → B x → C x) p f) by
subst-app {A = A} B C =
    elim
      (λ {x y} p → (f : B x → C x) {bx : B x} {by : B y} (q : subst B p bx ≡ by) →
              subst C p (f bx) ≡ (subst (λ x → B x → C x) p f) by)
      (λ x f → elim
          (λ {bx by} q → subst C (refl x) (f bx) ≡ (subst (λ x → B x → C x) (refl x) f) by)
          (λ b → refl _))

subst-path[id] : ∀ {ℓ₁} {A : Set ℓ₁} (f : A → A)
                 {x y : A} (p : x ≡ y) (q : f x ≡ x) →
                 subst (λ x → f x ≡ x) p q ≡ trans (sym (cong f p)) (trans q p)
subst-path[id] f =
  elim
    (λ {x y} (p : x ≡ y) → (q : f x ≡ x) →
        subst (λ x → f x ≡ x) p q ≡ trans (sym (cong f p)) (trans q p))
    (λ x q →
        subst (λ x → f x ≡ x) (refl _) q                    ≡⟨ refl _ ⟩
        q                                                   ≡⟨ sym $ trans-reflʳ q ⟩∎
--      (trans q (refl _))                                  ≡⟨ refl _ ⟩
--      trans (refl _) (trans q (refl _))                   ≡⟨ refl _ ⟩
--      trans (sym (refl _)) (trans q (refl _))             ≡⟨ refl _ ⟩
        trans (sym (cong f (refl _))) (trans q (refl _))    ∎)

subst-path[simp₂] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f g : A → B)
              {x y : A} (p : x ≡ y) (q : f x ≡ g x) →
              subst (λ x → f x ≡ g x) p q ≡ trans (sym (cong f p)) (trans q (cong g p))
subst-path[simp₂] f g =
  elim
    (λ {x y} (p : x ≡ y) → (q : f x ≡ g x) →
        subst (λ x → f x ≡ g x) p q ≡ trans (sym (cong f p)) (trans q (cong g p)))
    (λ x q →
        subst (λ x → f x ≡ g x) (refl _) q                        ≡⟨ refl _ ⟩
        q                                                         ≡⟨ sym $ trans-reflʳ q ⟩∎
--      (trans q (refl _))                                        ≡⟨ refl _ ⟩
--      trans (refl _) (trans q (refl _))                         ≡⟨ refl _ ⟩
--      trans (sym (refl _)) (trans q (refl _))                   ≡⟨ refl _ ⟩
--      trans (sym (cong f (refl _))) (trans q (refl _))          ≡⟨ refl _ ⟩∎
        trans (sym (cong f (refl _))) (trans q (cong g (refl _))) ∎)

-- Derived³ lemmas

cong[dep]-const : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B)
                  {x y : A} (p : x ≡ y) → cong[dep] (const B) f p ≡ (trans (subst-const p (f x)) (cong f p))
cong[dep]-const {B = B} f =
  elim
    (λ {x y} p → cong[dep] (const B) f p ≡ (trans (subst-const p (f x)) (cong f p)) )
    (λ x →
        cong[dep] (const B) f (refl x)                      ≡⟨ refl _ ⟩
        refl (f x)                                          ≡⟨ refl _ ⟩
        subst-const (refl x) (f x)                          ≡⟨ sym $ trans-reflʳ _ ⟩∎
--      trans (subst-const (refl x) (f x)) (refl _)         ≡⟨ refl _ ⟩∎
        trans (subst-const (refl x) (f x)) (cong f (refl _))∎)

trans-sym-trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} (p : y ≡ x) (q : x ≡ z) → trans (sym p) (trans p q) ≡ q
trans-sym-trans p q =
    trans (sym p) (trans p q)               ≡⟨ sym $ trans-assoc (sym p) _ _ ⟩
    trans (trans (sym p) p) q               ≡⟨ cong (λ p → trans p q) $ trans-symˡ p ⟩∎
--  trans (refl _) q                        ≡⟨ refl _ ⟩∎
    q                                       ∎

trans-transʳ-sym : ∀ {ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → trans p (trans (sym p) q) ≡ q
trans-transʳ-sym p q =
    trans p (trans (sym p) q)               ≡⟨ sym $ trans-assoc p _ _ ⟩
    trans (trans p (sym p)) q               ≡⟨ cong (λ p → trans p q) $ trans-symʳ p ⟩∎
--  trans (refl _) q                        ≡⟨ refl _ ⟩∎
    q                                       ∎

trans-trans-symʳ : ∀ {ℓ} {A : Set ℓ} {x y z : A} (q : x ≡ y) (p : z ≡ y) → trans (trans q (sym p)) p ≡ q
trans-trans-symʳ q p =
    trans (trans q (sym p)) p               ≡⟨ trans-assoc q _ _ ⟩
    trans q (trans (sym p) p)               ≡⟨ cong (trans q) $ trans-symˡ p ⟩
    trans q (refl _)                        ≡⟨ trans-reflʳ _ ⟩∎
    q                                       ∎

trans-trans-symʳʳ : ∀ {ℓ} {A : Set ℓ} {x y z : A} (q : x ≡ y) (p : y ≡ z) → trans (trans q p) (sym p) ≡ q
trans-trans-symʳʳ q p =
    trans (trans q p) (sym p)               ≡⟨ trans-assoc q _ _ ⟩
    trans q (trans p (sym p))               ≡⟨ cong (trans q) $ trans-symʳ p ⟩
    trans q (refl _)                        ≡⟨ trans-reflʳ _ ⟩∎
    q                                       ∎


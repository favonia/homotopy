------------------------------------------------------------------------
-- Free groups
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

module Space.FreeGroup where

open import Prelude

open import Path
open import Path.Lemmas

open import Space.Fin.Lemmas as F
open import Space.List.Lemmas as L

-- ... was Alphabet n = Fin n ⊎ Fin n before
data Alphabet (n : ℕ) : Set where
  gen : Fin n → Alphabet n
  inv : Fin n → Alphabet n

Word : ℕ → Set
Word n = List (Alphabet n)

-- Positive definition (following Dan Licata's advice)
data Stable {n} : Alphabet n → Alphabet n → Set where
  gen-gen : ∀ {x y} → Stable (gen x) (gen y)
  inv-inv : ∀ {x y} → Stable (inv x) (inv y)
  gen-inv : ∀ {x y} → ¬ x ≡ y → Stable (gen x) (inv y)
  inv-gen : ∀ {x y} → ¬ x ≡ y → Stable (inv x) (gen y)

decideStable : ∀ {n} (x y : Alphabet n) → Dec (Stable x y)
decideStable (gen x) (gen y) = inj₁ gen-gen
decideStable (inv x) (inv y) = inj₁ inv-inv
decideStable {n} (gen x) (inv y) with F.decide-≡ x y
... | inj₁ eq  = inj₂ λ{(gen-inv neq) → neq eq}
... | inj₂ neq = inj₁ $ gen-inv neq
decideStable {n} (inv x) (gen y) with F.decide-≡ x y
... | inj₁ eq  = inj₂ λ{(inv-gen neq) → neq eq}
... | inj₂ neq = inj₁ $ inv-gen neq

-- Positive definition (following Dan Licata's advice)
data Normalized {n} : Word n → Set where
  empty   : Normalized []
  single  : ∀ {x} → Normalized [ x ]
  cons    : ∀ {x₁ x₂} {xs} → Stable x₁ x₂ →
              Normalized (x₂ ∷ xs) →
              Normalized (x₁ ∷ x₂ ∷ xs)

Free : ℕ → Set
Free n = Σ (Word n) Normalized

private
  ------------------------------------------------------------------------
  -- rev-append and append

  word-rev-append : ∀ {n} → Word n → Word n → Word n
  word-rev-append []       w        = w
  word-rev-append (x ∷ xs) []       = word-rev-append xs (x ∷ [])
  word-rev-append (x ∷ xs) (y ∷ ys) with decideStable x y
  ... | inj₁ stable   = word-rev-append xs (x ∷ y ∷ ys)
  ... | inj₂ unstable = word-rev-append xs ys

  norm-tail : ∀ {n} {x} {xs : Word n} →
                Normalized (x ∷ xs) → Normalized xs
  norm-tail single      = empty
  norm-tail (cons _ n)  = n

  norm-rev-append : ∀ {n} (xs ys : Word n) → Normalized ys →
                      Normalized (word-rev-append xs ys)
  norm-rev-append []       ys       n     = n
  norm-rev-append (x ∷ xs) []       empty = norm-rev-append xs [ x ] single
  norm-rev-append (x ∷ xs) (y ∷ ys) n with decideStable x y
  ... | inj₁ stable   = norm-rev-append xs (x ∷ y ∷ ys) (cons stable n)
  ... | inj₂ unstable = norm-rev-append xs ys (norm-tail n)

  word-rev : ∀ {n} → Word n → Word n
  word-rev w = word-rev-append w []

  stable-sym : ∀ {n} {x y : Alphabet n} → Stable x y → Stable y x
  stable-sym gen-gen = gen-gen
  stable-sym inv-inv = inv-inv
  stable-sym (gen-inv neq) = inv-gen $ neq ∘ sym
  stable-sym (inv-gen neq) = gen-inv $ neq ∘ sym

  data HeadStable {n} : Word n → Word n → Set where
    heads : ∀ {x y} {xs ys} → Stable x y →
              HeadStable (x ∷ xs) (y ∷ ys)
    left  : ∀ {xs} → HeadStable xs []
    right : ∀ {xs} → HeadStable [] xs

  norm-head : ∀ {n} {x} {xs ys : Word n} →
                Normalized (x ∷ xs) → HeadStable (x ∷ ys) xs
  norm-head single      = left
  norm-head (cons s _)  = heads s

  head-stable-sym : ∀ {n} {xs ys : Word n} → HeadStable xs ys → HeadStable ys xs
  head-stable-sym left = right
  head-stable-sym right = left
  head-stable-sym (heads s) = heads $ stable-sym s

  word-rev-append-head-stable  : ∀ {n} x xs (ys : Word n) → HeadStable (x ∷ xs) ys →
                              word-rev-append (x ∷ xs) ys ≡ word-rev-append xs (x ∷ ys)
  word-rev-append-head-stable x xs []       _         = refl _
  word-rev-append-head-stable x xs (y ∷ ys) (heads s) with decideStable x y
  ... | inj₁ _ = refl _
  ... | inj₂ u = ⊥-elim $ u s

  word-rev-rev-append : ∀ {n} (xs ys : Word n) →
                          Normalized xs → HeadStable xs ys →
                          word-rev (word-rev-append xs ys) ≡ word-rev-append ys xs
  word-rev-rev-append []       ys _ _  = refl _
  word-rev-rev-append (x ∷ xs) ys n hs =
    word-rev (word-rev-append (x ∷ xs) ys) 
      ≡⟨ cong word-rev $ word-rev-append-head-stable x xs ys hs ⟩
    word-rev (word-rev-append xs (x ∷ ys))
      ≡⟨ word-rev-rev-append xs (x ∷ ys) (norm-tail n) (head-stable-sym $ norm-head n) ⟩
    word-rev-append (x ∷ ys) xs
      ≡⟨ word-rev-append-head-stable x ys xs $ norm-head n ⟩∎
    word-rev-append ys (x ∷ xs)
      ∎

  word-rev-rev : ∀ {n} (xs : Word n) → Normalized xs → word-rev (word-rev xs) ≡ xs
  word-rev-rev xs n = word-rev-rev-append xs [] n left

  word-append : ∀ {n} → Word n → Word n → Word n
  word-append w₁ w₂ = word-rev-append (word-rev w₁) w₂

  norm-append : ∀ {n} (xs ys : Word n) → Normalized ys →
                  Normalized (word-append xs ys)
  norm-append xs ys n = norm-rev-append (word-rev xs) ys n

  ------------------------------------------------------------------------
  -- flip

  alphabet-flip : ∀ {n} → Alphabet n → Alphabet n
  alphabet-flip (gen x) = inv x
  alphabet-flip (inv x) = gen x

  alphabet-flip-flip : ∀ {n} (x : Alphabet n) → alphabet-flip (alphabet-flip x) ≡ x
  alphabet-flip-flip (gen x) = refl _
  alphabet-flip-flip (inv x) = refl _

  stable-flip : ∀ {n} {x₁ x₂ : Alphabet n} → Stable x₁ x₂ →
                  Stable (alphabet-flip x₁) (alphabet-flip x₂)
  stable-flip gen-gen       = inv-inv
  stable-flip inv-inv       = gen-gen
  stable-flip (gen-inv neq) = inv-gen neq
  stable-flip (inv-gen neq) = gen-inv neq

  stable-flip-back : ∀ {n} {x₁ x₂ : Alphabet n} →
                      Stable (alphabet-flip x₁) (alphabet-flip x₂) →
                      Stable x₁ x₂
  stable-flip-back s =
    subst id (cong₂ Stable (alphabet-flip-flip _) (alphabet-flip-flip _)) $
      stable-flip s

  word-flip : ∀ {n} → Word n → Word n
  word-flip []       = []
  word-flip (x ∷ xs) = alphabet-flip x ∷ word-flip xs
  
  word-flip-flip : ∀ {n} (xs : Word n) → word-flip (word-flip xs) ≡ xs
  word-flip-flip []       = refl _
  word-flip-flip (x ∷ xs) = cong₂ (λ x xs → x ∷ xs) (alphabet-flip-flip x) (word-flip-flip xs)

  norm-flip : ∀ {n} {xs : Word n} → Normalized xs →
                Normalized (word-flip xs)
  norm-flip empty       = empty
  norm-flip single      = single
  norm-flip (cons s n)  = cons (stable-flip s) $ norm-flip n

  ------------------------------------------------------------------------
  -- inverse

  word-inverse : ∀ {n} → Word n → Word n
  word-inverse w = word-rev $ word-flip w

  word-rev-append-flipʳ : ∀ {n} (xs : Word n) → word-rev-append xs (word-flip xs) ≡ []
  word-rev-append-flipʳ []           = refl _
  word-rev-append-flipʳ (gen x ∷ xs) with F.decide-≡ x x
  ... | inj₁ _   = word-rev-append-flipʳ xs
  ... | inj₂ neq = ⊥-elim $ neq $ refl _
  word-rev-append-flipʳ (inv x ∷ xs) with F.decide-≡ x x
  ... | inj₁ _   = word-rev-append-flipʳ xs
  ... | inj₂ neq = ⊥-elim $ neq $ refl _
  
  word-rev-append-flipˡ : ∀ {n} (xs : Word n) → word-rev-append (word-flip xs) xs ≡ []
  word-rev-append-flipˡ xs =
    word-rev-append (word-flip xs) xs
      ≡⟨ cong (word-rev-append $ word-flip xs) $ sym $ word-flip-flip xs ⟩
    word-rev-append (word-flip xs) (word-flip $ word-flip xs)
      ≡⟨ word-rev-append-flipʳ $ word-flip xs ⟩∎
    []
      ∎

  word-inverse-append : ∀ {n} (xs : Word n) → Normalized xs →
                          word-append (word-inverse xs) xs ≡ []
  word-inverse-append xs n =
    word-append (word-inverse xs) xs
      ≡⟨ cong (λ xs₁ → word-rev-append xs₁ xs) $ word-rev-rev (word-flip xs) (norm-flip n) ⟩
    word-rev-append (word-flip xs) xs
      ≡⟨ word-rev-append-flipˡ xs ⟩∎
    []
      ∎

  word-flip-rev-append : ∀ {n} (xs ys : Word n) →
                          word-flip (word-rev-append xs ys) ≡
                          word-rev-append (word-flip xs) (word-flip ys)
  word-flip-rev-append []       ys       = refl _
  word-flip-rev-append (x ∷ xs) []       = word-flip-rev-append xs [ x ]
  word-flip-rev-append (x ∷ xs) (y ∷ ys) with decideStable x y | decideStable (alphabet-flip x) (alphabet-flip y)
  ... | inj₁ _ | inj₁ _ = word-flip-rev-append xs (x ∷ y ∷ ys)
  ... | inj₂ _ | inj₂ _ = word-flip-rev-append xs ys
  ... | inj₁ s | inj₂ u = ⊥-elim $ u (stable-flip s)
  ... | inj₂ u | inj₁ s = ⊥-elim $ u (stable-flip-back s)
  
  word-append-inverse : ∀ {n} (xs : Word n) →
                          word-append xs (word-inverse xs) ≡ []
  word-append-inverse xs =
    word-append xs (word-rev (word-flip xs))
      ≡⟨ cong (λ xs₂ → word-append xs xs₂) $ sym $ word-flip-rev-append xs [] ⟩
    word-append xs (word-flip (word-rev xs))
      ≡⟨ word-rev-append-flipʳ (word-rev xs) ⟩∎
    []
      ∎

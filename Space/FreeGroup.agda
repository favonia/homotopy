------------------------------------------------------------------------
-- Free groups
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

open import Univalence

module Space.FreeGroup
  (univ : ∀ {ℓ} (A B : Set ℓ) → Univalence-axiom A B) where

open import Prelude renaming (_∘_ to _⊙_)

open import Path
open import Path.Sum
open import Path.Lemmas

import Univalence.Lemmas; open Univalence.Lemmas univ

open import Space.Fin.Lemmas as F
open import Space.List.Lemmas as L

-- ... was Alphabet n = Fin n ⊎ Fin n before
data Alphabet (n : ℕ) : Set where
  gen : Fin n → Alphabet n
  inv : Fin n → Alphabet n

alphabet-flip : ∀ {n} → Alphabet n → Alphabet n
alphabet-flip (gen x) = inv x
alphabet-flip (inv x) = gen x

Word : ℕ → Set
Word n = List (Alphabet n)

-- Positive definition (following Dan Licata's advice)
data Stable {n} : Alphabet n → Alphabet n → Set where
  gen-gen : ∀ {x y} → Stable (gen x) (gen y)
  inv-inv : ∀ {x y} → Stable (inv x) (inv y)
  gen-inv : ∀ {x y} → x <> y → Stable (gen x) (inv y)
  inv-gen : ∀ {x y} → x <> y → Stable (inv x) (gen y)

data Unstable {n} : Alphabet n → Alphabet n → Set where
  gen-inv : ∀ {x} → Unstable (gen x) (inv x)
  inv-gen : ∀ {x} → Unstable (inv x) (gen x)

decideStable : ∀ {n} (x y : Alphabet n) → Stable x y ⊎ Unstable x y
decideStable (gen x) (gen y) = inj₁ gen-gen
decideStable (inv x) (inv y) = inj₁ inv-inv
decideStable {n} (gen x) (inv y) with F.decide-≡' x y
... | inj₁ eq  = inj₂ $ subst (λ y → Unstable (gen x) (inv y)) eq gen-inv
... | inj₂ neq = inj₁ $ gen-inv neq
decideStable {n} (inv x) (gen y) with F.decide-≡' x y
... | inj₁ eq  = inj₂ $ subst (λ y → Unstable (inv x) (gen y)) eq inv-gen
... | inj₂ neq = inj₁ $ inv-gen neq

-- Positive definition (following Dan Licata's advice)
data Normalized {n} : Word n → Set where
  ∅   : Normalized []
  ✭   : ∀ {x} → Normalized [ x ]
  _▸_ : ∀ {x₁ x₂} {xs} → Stable x₁ x₂ →
          Normalized (x₂ ∷ xs) →
          Normalized (x₁ ∷ x₂ ∷ xs)

FreeGroup : ℕ → Set
FreeGroup n = Σ (Word n) Normalized

------------------------------------------------------------------------
-- misc

stable-sym : ∀ {n} {x y : Alphabet n} → Stable x y → Stable y x
stable-sym gen-gen = gen-gen
stable-sym inv-inv = inv-inv
stable-sym (gen-inv neq) = inv-gen $ <>-sym neq
stable-sym (inv-gen neq) = gen-inv $ <>-sym neq

private
  unstable⇒flip : ∀ {n} {x y z : Alphabet n} → Unstable x y → x ≡ alphabet-flip y
  unstable⇒flip gen-inv = refl _
  unstable⇒flip inv-gen = refl _

  unstable-sym : ∀ {n} {x y : Alphabet n} → Unstable x y → Unstable y x
  unstable-sym gen-inv = inv-gen
  unstable-sym inv-gen = gen-inv

  unstable-involutive : ∀ {n} {x y y' z : Alphabet n} → Unstable x y → Unstable y z → x ≡ z
  unstable-involutive us₁ us₂ = trans (unstable⇒flip us₁) (sym $ unstable⇒flip $ unstable-sym us₂)

------------------------------------------------------------------------
-- head, tail, cons

private
  data HeadStable {n} : Word n → Word n → Set where
    heads : ∀ {x y} {xs ys} → Stable x y →
              HeadStable (x ∷ xs) (y ∷ ys)
    left  : ∀ {xs} → HeadStable xs []
    right : ∀ {xs} → HeadStable [] xs

  norm-head : ∀ {n} {x} {xs xxs : Word n} → xxs ≡ x ∷ xs →
                Normalized xxs → ∀ ys → HeadStable xs (x ∷ ys)
  norm-head _ ✭       _ = right
  norm-head _ (s ▸ _) _ = heads $ stable-sym s

  norm-tail : ∀ {n} {x} {xs : Word n} →
                Normalized (x ∷ xs) → Normalized xs
  norm-tail (✭ _)   = ∅
  norm-tail (_ ▸ n) = n

  norm-cons : ∀ {n} {x} {xs ys : Word n} → HeadStable (x ∷ xs) ys → Normalized ys →
                Normalized (x ∷ ys)
  norm-cons left      ∅ = ✭
  norm-cons (heads s) n = s ▸ n

------------------------------------------------------------------------
-- head-reduce

private
  word-head-reduce : ∀ {n} → Alphabet n → Word n → Word n
  word-head-reduce x [] = [ x ]
  word-head-reduce x (y ∷ ys) with decideStable x y
  ... | inj₁ _ = x ∷ y ∷ ys
  ... | inj₂ _ = ys

  norm-head-reduce : ∀ {n} x {xs : Word n} → Normalized xs →
                      Normalized (word-head-reduce x xs)
  norm-head-reduce x         ∅ = ✭
  norm-head-reduce x {y ∷ _} n with decideStable x y
  ... | inj₁ s = s ▸ n
  ... | inj₂ _ = norm-tail n

  word-head-reduce-¬stable : ∀ {n} {x y : Alphabet n} → ¬ Stable x y →
                             ∀ {ys} → word-head-reduce x (y ∷ ys) ≡ ys
  word-head-reduce-¬stable {x = x} {y} ¬s with decideStable x y
  ... | inj₁ s = ⊥-elim $ ¬s s
  ... | inj₂ _ = refl _

  word-head-reduce₂-¬stable : ∀ {n} {x y : Alphabet n} → ¬ Stable x y →
                              ∀ {zs} → Normalized zs →
                                word-head-reduce x (word-head-reduce y zs) ≡ zs
  word-head-reduce₂-¬stable {x = x} {y} nsxy ∅ with decideStable x y
  ... | inj₁ s = ⊥-elim $ nsxy s
  ... | inj₂ _ = refl _
  word-head-reduce₂-¬stable {x = x} {y} nsxy {z ∷ []} ✭ with decideStable y z
  ... | inj₂ nsyz = cong [_] $ unstable-involutive nsxy nsyz
  ... | inj₁ _ with decideStable x y
  ...   | inj₁ s = ⊥-elim $ nsxy s
  ...   | inj₂ _ = refl _
  word-head-reduce₂-¬stable {x = x} {y} nsxy {z₁ ∷ z₂ ∷ zs} (s ▸ _) with decideStable y z₁
  ... | inj₁ _ with decideStable x y
  ...   | inj₁ sxy = ⊥-elim $ nsxy sxy
  ...   | inj₂ _   = refl _
  word-head-reduce₂-¬stable {x = x} {y} nsxy {z₁ ∷ z₂ ∷ zs} (s ▸ _) | inj₂ u with decideStable x z₂
  ...   | inj₁ _  = cong (λ x → x ∷ z₂ ∷ zs) $ unstable-involutive nsxy u
  ...   | inj₂ u₂ = ⊥-elim $ subst (λ x → ¬ Stable x z₂) (unstable-involutive nsxy u) u₂ s

  word-head-reduce₂-stable : ∀ {n} x₁ x₂ (xs : Word n) → Stable x₁ x₂ →
                          word-head-reduce x₁ (x₂ ∷ xs) ≡ x₁ ∷ x₂ ∷ xs
  word-head-reduce₂-stable x₁ x₂ x s with decideStable x₁ x₂
  ... | inj₁ _ = refl _
  ... | inj₂ u = ⊥-elim $ u s

------------------------------------------------------------------------
-- append-reduce

private
  word-append-reduce : ∀ {n} → Word n → Word n → Word n
  word-append-reduce xs ys = foldr word-head-reduce ys xs

  norm-append-reduce : ∀ {n} xs {ys : Word n} → Normalized ys →
                        Normalized (word-append-reduce xs ys)
  norm-append-reduce []       n = n
  norm-append-reduce (x ∷ xs) n = norm-head-reduce x $ norm-append-reduce xs n

  word-snoc-append-reduce : ∀ {n} xs x (ys : Word n) →
                              word-append-reduce (snoc xs x) ys ≡
                              word-append-reduce xs (word-head-reduce x ys)
  word-snoc-append-reduce []        x′ ys = refl _
  word-snoc-append-reduce (x ∷ xs)  x′ ys =
    cong (word-head-reduce x) $ word-snoc-append-reduce xs x′ ys

  word-append-reduce-head-reduce : ∀ {n} x (ys : Word n) {zs} → Normalized zs →
    word-append-reduce (word-head-reduce x ys) zs ≡
    word-head-reduce x (word-append-reduce ys zs)
  word-append-reduce-head-reduce _ []       _  = refl _
  word-append-reduce-head-reduce x (y ∷ ys) nz with decideStable x y
  ... | inj₁ _ = refl _
  ... | inj₂ u = sym $ word-head-reduce₂-¬stable u (norm-append-reduce ys nz)

  word-append-reduce-assoc : ∀ {n} (xs ys : Word n) {zs} → Normalized zs →
    word-append-reduce (word-append-reduce xs ys) zs ≡
    word-append-reduce xs (word-append-reduce ys zs)
  word-append-reduce-assoc []       _       nz = refl _
  word-append-reduce-assoc (x ∷ xs) ys {zs} nz =
    word-append-reduce (word-head-reduce x $ word-append-reduce xs ys) zs
      ≡⟨ word-append-reduce-head-reduce x (word-append-reduce xs ys) nz ⟩
    word-head-reduce x (word-append-reduce (word-append-reduce xs ys) zs)
      ≡⟨ cong (word-head-reduce x) $ word-append-reduce-assoc xs ys nz ⟩∎
    word-head-reduce x (word-append-reduce xs $ word-append-reduce ys zs)
      ∎

  word-append-reduce-[] : ∀ {n} {xs : Word n} → Normalized xs →
                          word-append-reduce xs [] ≡ xs
  word-append-reduce-[]                     ∅       = refl _
  word-append-reduce-[]                     ✭       = refl _
  word-append-reduce-[] {xs = x₁ ∷ x₂ ∷ xs} (s ▸ n) =
    word-head-reduce x₁ (word-append-reduce (x₂ ∷ xs) [])
      ≡⟨ cong (word-head-reduce x₁) $ word-append-reduce-[] n ⟩
    word-head-reduce x₁ (x₂ ∷ xs)
      ≡⟨ word-head-reduce₂-stable x₁ x₂ xs s ⟩∎
    x₁ ∷ x₂ ∷ xs
      ∎

------------------------------------------------------------------------
-- rev

private
  private
    lemma₀ : ∀ {n} (xs ys : Word n) → Normalized xs → Normalized ys → HeadStable xs ys →
                    Normalized (rev xs ++ ys)
    lemma₀ []       ys _  ny _  = ny
    lemma₀ (x ∷ xs) ys nx ny hs =
      subst Normalized (sym $ snoc-++ (rev xs) x ys) $
        lemma₀ xs (x ∷ ys) (norm-tail nx) (norm-cons hs ny) (norm-head nx ys)

  norm-rev-++ : ∀ {n} {xs ys : Word n} → Normalized xs → Normalized ys → HeadStable xs ys →
                  Normalized (rev xs ++ ys)
  norm-rev-++ nx ny hs = lemma₀ _ _ nx ny hs

  norm-rev : ∀ {n} {xs : Word n} → Normalized xs → Normalized (rev xs)
  norm-rev nx = subst Normalized (++-[] _) $ norm-rev-++ nx ∅ left

------------------------------------------------------------------------
-- flip

  alphabet-flip-flip : ∀ {n} (x : Alphabet n) → alphabet-flip (alphabet-flip x) ≡ x
  alphabet-flip-flip (gen x) = refl _
  alphabet-flip-flip (inv x) = refl _

  stable-flip : ∀ {n} {x₁ x₂ : Alphabet n} → Stable x₁ x₂ →
                  Stable (alphabet-flip x₁) (alphabet-flip x₂)
  stable-flip gen-gen       = inv-inv
  stable-flip inv-inv       = gen-gen
  stable-flip (gen-inv neq) = inv-gen neq
  stable-flip (inv-gen neq) = gen-inv neq

  stable-flip⁻¹ : ∀ {n} {x₁ x₂ : Alphabet n} →
                      Stable (alphabet-flip x₁) (alphabet-flip x₂) →
                      Stable x₁ x₂
  stable-flip⁻¹ s =
    subst id (cong₂ Stable (alphabet-flip-flip _) (alphabet-flip-flip _)) $
      stable-flip s

  word-flip : ∀ {n} → Word n → Word n
  word-flip xs = map alphabet-flip xs

  word-flip-flip : ∀ {n} (xs : Word n) → word-flip (word-flip xs) ≡ xs
  word-flip-flip []       = refl _
  word-flip-flip (x ∷ xs) = cong₂ (λ x xs → x ∷ xs) (alphabet-flip-flip x) (word-flip-flip xs)

  norm-flip : ∀ {n} {xs : Word n} → Normalized xs →
                Normalized (word-flip xs)
  norm-flip ∅       = ∅
  norm-flip ✭       = ✭
  norm-flip (s ▸ n) = stable-flip s ▸ norm-flip n

  word-flip-snoc : ∀ {n} (xs : Word n) y → word-flip (snoc xs y) ≡ snoc (word-flip xs) (alphabet-flip y)
  word-flip-snoc []       _ = refl _
  word-flip-snoc (x ∷ xs) y = cong (λ zs → alphabet-flip x ∷ zs) $ word-flip-snoc xs y

  word-flip-rev : ∀ {n} (xs : Word n) → word-flip (rev xs) ≡ rev (word-flip xs)
  word-flip-rev []       = refl _
  word-flip-rev (x ∷ xs) =
    word-flip (snoc (rev xs) x)
      ≡⟨ word-flip-snoc (rev xs) x ⟩
    snoc (word-flip $ rev xs) (alphabet-flip x)
      ≡⟨ cong (λ xs → snoc xs (alphabet-flip x)) $ word-flip-rev xs ⟩∎
    snoc (rev $ word-flip xs) (alphabet-flip x)
      ∎

  ¬stable-flipˡ : ∀ {n} (x : Alphabet n) → ¬ Stable (alphabet-flip x) x
  ¬stable-flipˡ (gen x) s = ¬stable-inv-gen (refl _) s
    where
      ¬stable-inv-gen : ∀ {n} {i j : Fin n} → i ≡ j → ¬ Stable (inv i) (gen j)
      ¬stable-inv-gen eq (inv-gen neq) = neq eq
  ¬stable-flipˡ (inv x) s = ¬stable-gen-inv (refl _) s
    where
      ¬stable-gen-inv : ∀ {n} {i j : Fin n} → i ≡ j → ¬ Stable (gen i) (inv j)
      ¬stable-gen-inv eq (gen-inv neq) = neq eq

  ¬stable-flipʳ : ∀ {n} (x : Alphabet n) → ¬ Stable x (alphabet-flip x)
  ¬stable-flipʳ x = ¬stable-flipˡ x ⊙ stable-sym

------------------------------------------------------------------------
-- inverse

private
  word-inverse : ∀ {n} → Word n → Word n
  word-inverse xs = rev $ word-flip xs

  word-inverse-inverse : ∀ {n} (xs : Word n) → word-inverse (word-inverse xs) ≡ xs
  word-inverse-inverse xs =
    rev (word-flip $ rev $ word-flip xs)
      ≡⟨ cong rev $ word-flip-rev $ word-flip xs ⟩
    (rev $ rev $ word-flip $ word-flip xs)
      ≡⟨ rev-rev (word-flip $ word-flip xs) ⟩
    (word-flip $ word-flip xs)
      ≡⟨ word-flip-flip xs ⟩∎
    xs
      ∎

  norm-inverse : ∀ {n} {xs : Word n} → Normalized xs → Normalized (word-inverse xs)
  norm-inverse n = norm-rev $ norm-flip n

  private
    lemma₁ : ∀ {n} x (xs : Word n) → word-head-reduce (alphabet-flip x) (x ∷ xs) ≡ xs
    lemma₁ (gen x) xs with F.decide-≡ x x
    ... | inj₁ _   = refl _
    ... | inj₂ neq = ⊥-elim $ neq $ refl _
    lemma₁ (inv x) xs with F.decide-≡ x x
    ... | inj₁ _   = refl _
    ... | inj₂ neq = ⊥-elim $ neq $ refl _

  word-inverse-append-reduce : ∀ {n} (xs : Word n) → word-append-reduce (word-inverse xs) xs ≡ []
  word-inverse-append-reduce []       = refl _
  word-inverse-append-reduce (x ∷ xs) =
    word-append-reduce (snoc (word-inverse xs) (alphabet-flip x)) (x ∷ xs)
      ≡⟨ word-snoc-append-reduce (word-inverse xs) (alphabet-flip x) (x ∷ xs) ⟩
    word-append-reduce (word-inverse xs) (word-head-reduce (alphabet-flip x) (x ∷ xs))
      ≡⟨ cong (word-append-reduce (word-inverse xs)) $ lemma₁ x xs ⟩
    word-append-reduce (word-inverse xs) xs
      ≡⟨ word-inverse-append-reduce xs ⟩∎
    []
      ∎

  word-append-reduce-inverse : ∀ {n} (xs : Word n) → word-append-reduce xs (word-inverse xs) ≡ []
  word-append-reduce-inverse xs =
    word-append-reduce xs (word-inverse xs)
      ≡⟨ cong (λ xs₁ → word-append-reduce xs₁ (word-inverse xs)) $ sym $ word-inverse-inverse xs ⟩
    word-append-reduce (word-inverse $ word-inverse xs) (word-inverse xs)
      ≡⟨ word-inverse-append-reduce (word-inverse xs) ⟩∎
    []
      ∎

------------------------------------------------------------------------
-- the public interface for a group

unit : ∀ {n} → FreeGroup n
unit = [] , ∅

_∘_ : ∀ {n} → FreeGroup n → FreeGroup n → FreeGroup n
(xs₁ , n₁) ∘ (xs₂ , n₂) = word-append-reduce xs₁ xs₂ , norm-append-reduce xs₁ n₂

private
  unique-stable-proof : ∀ {n} {x y : Alphabet n} (s₁ s₂ : Stable x y) → s₁ ≡ s₂
  unique-stable-proof gen-gen        gen-gen        = refl _
  unique-stable-proof inv-inv        inv-inv        = refl _
  unique-stable-proof (gen-inv neq₁) (gen-inv neq₂) = cong gen-inv $ unique-neq-proof neq₁ neq₂
  unique-stable-proof (inv-gen neq₁) (inv-gen neq₂) = cong inv-gen $ unique-neq-proof neq₁ neq₂

  unique-normalized-proof : ∀ {n} {xs : Word n} (n₁ n₂ : Normalized xs) → n₁ ≡ n₂
  unique-normalized-proof ∅         ∅         = refl _
  unique-normalized-proof ✭         ✭         = refl _
  unique-normalized-proof (s₁ ▸ n₁) (s₂ ▸ n₂) =
    cong₂ _▸_ (unique-stable-proof s₁ s₂) (unique-normalized-proof n₁ n₂)

word-≡⇒free-group-≡ : ∀ {n} {f₁ f₂ : FreeGroup n} → proj₁ f₁ ≡ proj₁ f₂ → f₁ ≡ f₂
word-≡⇒free-group-≡ {f₁ = xs₁ , n₁} {f₂ = xs₂ , n₂} eq =
  Σ≡⇒≡Σ Normalized $ eq , unique-normalized-proof (subst Normalized eq n₁) n₂

∘-unitˡ : ∀ {n} (f : FreeGroup n) → unit ∘ f ≡ f
∘-unitˡ _ = refl _

∘-unitʳ : ∀ {n} (f : FreeGroup n) → f ∘ unit ≡ f
∘-unitʳ (_ , n) = word-≡⇒free-group-≡ $ word-append-reduce-[] n

∘-assoc : ∀ {n} (f₁ f₂ f₃ : FreeGroup n) → (f₁ ∘ f₂) ∘ f₃ ≡ f₁ ∘ (f₂ ∘ f₃)
∘-assoc (xs₁ , _) (xs₂ , _) (_ , n₃) =
  word-≡⇒free-group-≡ $ word-append-reduce-assoc xs₁ xs₂ n₃

_⁻¹ : ∀ {n} → FreeGroup n → FreeGroup n
(xs , n) ⁻¹ = word-inverse xs , norm-inverse n

∘-invˡ : ∀ {n} (f : FreeGroup n) → (f ⁻¹) ∘ f ≡ unit
∘-invˡ (xs , _) = word-≡⇒free-group-≡ $ word-inverse-append-reduce xs

∘-invʳ : ∀ {n} (f : FreeGroup n) → f ∘ (f ⁻¹) ≡ unit
∘-invʳ (xs , _) = word-≡⇒free-group-≡ $ word-append-reduce-inverse xs

cons : ∀ {n} → Alphabet n → FreeGroup n → FreeGroup n
cons x (xs , n) = word-head-reduce x xs , norm-head-reduce x n

private
  cons₂-stable′ : ∀ {n} {x y} (s : Stable x y) (ys : Word n) →
                   word-head-reduce x (y ∷ ys) ≡ x ∷ y ∷ ys
  cons₂-stable′ {x = x} {y} s ys with decideStable x y
  ... | inj₁ _ = refl _
  ... | inj₂ u = ⊥-elim $ u s

cons-stable : ∀ {n} {x y} (s : Stable x y) {ys : Word n} n →
                 cons x (y ∷ ys , n) ≡ (x ∷ y ∷ ys , s ▸ n)
cons-stable s {ys} _ = word-≡⇒free-group-≡ $ cons₂-stable′ s ys

cons-¬stable : ∀ {n} {x y} (us : ¬ Stable x y) {ys : Word n} {n} →
                 cons x (y ∷ ys , n) ≡ (ys , norm-tail n)
cons-¬stable ¬s = word-≡⇒free-group-≡ $ word-head-reduce-¬stable ¬s

cons₂-flipʳ : ∀ {n} x (f : FreeGroup n) → cons x (cons (alphabet-flip x) f) ≡ f
cons₂-flipʳ x (xs , n) = word-≡⇒free-group-≡ $ word-head-reduce₂-¬stable (¬stable-flipʳ x) n

cons₂-flipˡ : ∀ {n} x (f : FreeGroup n) → cons (alphabet-flip x) (cons x f) ≡ f
cons₂-flipˡ x (xs , n) = word-≡⇒free-group-≡ $ word-head-reduce₂-¬stable (¬stable-flipˡ x) n

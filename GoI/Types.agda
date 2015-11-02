module GoI.Types where

open import Level public

infix 5 _+_

data _+_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
     inl : (a : A) → A + B
     inr : (b : B) → A + B

+-swap : ∀ {a b} {A : Set a} {B : Set b} → A + B → B + A
+-swap (inl a) = inr a
+-swap (inr b) = inl b

+-assoc-l : ∀ {a b c} {A : Set a} {B : Set b} { C : Set c}
          → (A + B) + C → A + (B + C)
+-assoc-l (inl (inl a)) = inl a
+-assoc-l (inl (inr b)) = inr (inl b)
+-assoc-l (inr c) = inr (inr c)

+-assoc-r : ∀ {a b c} {A : Set a} {B : Set b} { C : Set c}
          → A + (B + C) → (A + B) + C
+-assoc-r (inl a) = inl (inl a)
+-assoc-r (inr (inl b)) = inl (inr b)
+-assoc-r (inr (inr c)) = inr c

infixr 4 _,_

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infixr 2 _×_

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

×-swap : ∀ {a b} {A : Set a} {B : Set b} → A × B → B × A
×-swap (a , b) = b , a

×-assoc-l : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          → (A × B) × C → A × (B × C)
×-assoc-l ((a , b) , c) = a , (b , c)

×-assoc-r : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          → A × (B × C) → (A × B) × C
×-assoc-r (a , (b , c)) = (a , b) , c

data ⊥ : Set where

⊥-elim : ∀ {ℓ} {A : Set ℓ} → ⊥ → A
⊥-elim ()

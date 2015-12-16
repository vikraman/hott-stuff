\AgdaHide{
\begin{code}
module GoI.Types where

open import Level public
\end{code}
}

We start by defining the empty, or \zero\ type,

\begin{code}
data ⊥ : Set where

⊥-elim : ∀ {ℓ} {A : Set ℓ} → ⊥ → A
⊥-elim ()
\end{code}

the sum type,

\AgdaHide{
\begin{code}
infixr 5 _+_
\end{code}
}
\begin{code}
data _+_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
     inl : (a : A) → A + B
     inr : (b : B) → A + B
\end{code}

and the product type in terms of the dependent sum type.

\AgdaHide{
\begin{code}
infixr 4 _,_
\end{code}
}
\begin{code}
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
\end{code}
\AgdaHide{
\begin{code}
open Σ public

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infixr 2 _×_
\end{code}
}
\begin{code}
_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B
\end{code}

\AgdaHide{
\begin{code}
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
\end{code}
}

\AgdaHide{
\begin{code}
×-swap : ∀ {a b} {A : Set a} {B : Set b} → A × B → B × A
×-swap (a , b) = b , a

×-assoc-l : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          → (A × B) × C → A × (B × C)
×-assoc-l ((a , b) , c) = a , (b , c)

×-assoc-r : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          → A × (B × C) → (A × B) × C
×-assoc-r (a , (b , c)) = (a , b) , c

distrib-ll : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
           → (C × A) + (C × B) → C × (A + B)
distrib-ll (inl (c , a)) = c , inl a
distrib-ll (inr (c , b)) = c , inr b

distrib-lr : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
           → C × (A + B) → (C × A) + (C × B)
distrib-lr (c , inl a) = inl (c , a)
distrib-lr (c , inr b) = inr (c , b)

distrib-rl : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
           → (A × C) + (B × C) → (A + B) × C
distrib-rl (inl (a , c)) = inl a , c
distrib-rl (inr (b , c)) = inr b , c

distrib-rr : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
           → (A + B) × C → (A × C) + (B × C)
distrib-rr (inl a , c) = inl (a , c)
distrib-rr (inr b , c) = inr (b , c)
\end{code}
}

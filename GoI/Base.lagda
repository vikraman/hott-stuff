\AgdaHide{
\begin{code}
module GoI.Base where

open import GoI.Types public
\end{code}
}

A Resumption takes an input and produces an output alongwith a new resumption. The type of resumptions is parameterized
by the sets of inputs $i$ and outputs $o$. An identity resumption doesn't change the input. We also need an elimination
form to assist Agda.

\begin{code}
data R {ℓ} (i : Set ℓ) : Set ℓ → Set (suc ℓ) where
     idᵣ : R i i
     r  : {o : Set ℓ} → (i → (o × R i o)) → R i o

R-elim : ∀ {ℓ} {i o : Set ℓ} → R i o → i → (o × R i o)
R-elim idᵣ x = x , idᵣ
R-elim (r f) v = f v
\end{code}
\AgdaHide{
\begin{code}
id-R : ∀ {ℓ} {A : Set ℓ} → R A A
id-R {ℓ} {A} = idᵣ

infixl 5 _>>_
\end{code}
}

Resumptions can be composed.

\begin{code}
_>>_ : ∀ {ℓ} {A B C : Set ℓ} → R A B → R B C → R A C
f >> idᵣ = f
idᵣ >> g = g
r f >> r g = r λ e → fst (g (fst (f e))) , snd (f e) >> snd (g (fst (f e)))
\end{code}

This makes \R\ a category of resumptions with $Set$s or types as objects, and resumptions as morphisms.

Using the sum type $A + B$, or disjoint union of $Set$s as the tensor product and $\bot$ as the identity, we can define
a symmetric monoidal structure on \R.

\AgdaHide{
\begin{code}
infixl 6 _**_
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
_**_ : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} {C D : Set ℓ₂} → R A B → R C D → R (A + C) (B + D)
idᵣ ** idᵣ = idᵣ
idᵣ ** r g = r λ { (inl a) → (inl a) , idᵣ ** r g
                 ; (inr c) → (inr (fst (g c))) , idᵣ ** snd (g c)
                 }
r f ** idᵣ = r λ { (inl a) → (inl (fst (f a))) , ((snd (f a)) ** idᵣ)
                 ; (inr c) → (inr c) , (r f) ** idᵣ
                 }
r f ** r g = r λ { (inl a) → (inl (fst (f a))) , ((snd (f a)) ** (r g))
                 ; (inr c) → (inr (fst (g c))) , ((r f) ** (snd (g c)))
                 }
\end{code}

We also add the feedback operation, or trace.

\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
trace : ∀ {ℓ} {A B C : Set ℓ} → R (A + B) (C + B) → R A C
loop : ∀ {ℓ} {A B C : Set ℓ} → R (A + B) (C + B) → A + B → C × R A C
trace f = r (λ a → loop f (inl a))
loop f v with R-elim f v
... | inl c , f' = c , trace f'
... | inr b , f' = loop f' (inr b)
\end{code}

The following are natural isomorphisms, the right unitor,

\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
ρ : ∀ {ℓ} {A : Set ℓ} → R (A + ⊥) A
ρ = r λ { (inl a) → a , ρ
        ; (inr ⊥) → (⊥-elim ⊥) , ρ
        }
\end{code}
\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
ρ' : ∀ {ℓ} {A : Set ℓ} → R A (A + ⊥)
ρ' = r λ { a → (inl a) , ρ' }
\end{code}
the left unitor,
\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
Λ : ∀ {ℓ} {A : Set ℓ} → R (⊥ + A) A
Λ = r λ { (inl ⊥) → (⊥-elim ⊥) , Λ
        ; (inr a) → a , Λ
        }
\end{code}
\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
Λ' : ∀ {ℓ} {A : Set ℓ} → R A (⊥ + A)
Λ' = r λ { a → (inr a) , Λ' }
\end{code}
the associator,
\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
α : ∀ {ℓ} {A B C : Set ℓ} → R ((A + B) + C) (A + (B + C))
α = r λ { (inl (inl a)) → (inl a) , α
        ; (inl (inr b)) → (inr (inl b)) , α
        ; (inr b) → (inr (inr b)) , α
        }
\end{code}
\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
α' : ∀ {ℓ} {A B C : Set ℓ} → R (A + (B + C)) ((A + B) + C)
α' = r λ { (inl a) → (inl (inl a)) , α'
         ; (inr (inl a)) → (inl (inr a)) , α'
         ; (inr (inr b)) → (inr b) , α'
         }
\end{code}
and the braiding.
\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
β : ∀ {ℓ} {A B : Set ℓ} → R (A + B) (B + A)
β = r λ { (inl a) → (inr a) , β
        ; (inr b) → (inl b) , β
        }
\end{code}
\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
β' : ∀ {ℓ} {A B : Set ℓ} → R (B + A) (A + B)
β' = r λ { (inl b) → (inr b) , β'
         ; (inr a) → (inl a) , β'
         }
\end{code}

This makes \R\ a symmetric monoidal category with trace.

We can now define a new category \G\ such that, the objects of \G\ are pairs $(A^+,A^-)$ of objects from \R\, and a
morphism $f: (A^+,A^-) \to (B^+,B^-)$ in \G\ is a morphism $f: A^+ \times B^- \to A^- \times B^+$ in \R.

\begin{code}
data G {ℓ} (A A' B B' : Set ℓ) : Set (suc ℓ) where
     g : R (A + B') (A' + B) → G A A' B B'
\end{code}

The identity object in \G\ is the symmetry isomorphism in \R.

\begin{code}
id-G : ∀ {ℓ} {A B : Set ℓ} → G A B A B
id-G = g β
\end{code}

Composition of isomorphisms in \G\ can be defined using trace in \R.

\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
assoc : ∀ {ℓ} {A B B' C' : Set ℓ} → R ((A + C') + (B' + B)) ((A + B') + (B + C'))
assoc = r λ { (inl (inl a)) → (inl (inl a)) , assoc
            ; (inl (inr b)) → (inr (inr b)) , assoc
            ; (inr (inl a)) → (inl (inr a)) , assoc
            ; (inr (inr b)) → (inr (inl b)) , assoc
            }
\end{code}
\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
assoc' : ∀ {ℓ} {A' B B' C : Set ℓ} → R ((A' + B) + (B' + C)) ((A' + C) + (B' + B))
assoc' = r λ { (inl (inl a)) → (inl (inl a)) , assoc'
             ; (inl (inr b)) → (inr (inr b)) , assoc'
             ; (inr (inl a)) → (inr (inl a)) , assoc'
             ; (inr (inr b)) → (inl (inr b)) , assoc'
             }
\end{code}
\AgdaHide{
\begin{code}
infixl 4 _>>>_
\end{code}
}
\begin{code}
_>>>_ : ∀ {ℓ} {A B C D E F : Set ℓ} → G A B C D → G C D E F → G A B E F
g f' >>> g g' = g (trace (assoc >> f' ** g' >> assoc'))
\end{code}

\G\ also admits a tensorial structure, given by

\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
γ : ∀ {ℓ} {A B C D : Set ℓ} → R ((A + B) + (C + D)) ((A + C) + (B + D))
γ = r λ { (inl (inl a)) → (inl (inl a)) , γ
        ; (inl (inr b)) → (inr (inl b)) , γ
        ; (inr (inl a)) → (inl (inr a)) , γ
        ; (inr (inr b)) → (inr (inr b)) , γ
        }
\end{code}
\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
γ' : ∀ {ℓ} {A B C D : Set ℓ} → R ((A + C) + (B + D)) ((A + B) + (C + D))
γ' = r λ { (inl (inl a)) → (inl (inl a)) , γ'
         ; (inl (inr b)) → (inr (inl b)) , γ'
         ; (inr (inl a)) → (inl (inr a)) , γ'
         ; (inr (inr b)) → (inr (inr b)) , γ'
         }
\end{code}
\AgdaHide{
\begin{code}
infixl 3 _++_
\end{code}
}
\begin{code}
_++_ : ∀ {ℓ} {A' B' C' D' E' F' G' H' : Set ℓ}
     → G A' B' C' D' → G E' F' G' H' → G (A' + E') (B' + F') (C' + G') (D' + H')
g f' ++ g g' = g (γ >> f' ** g' >> γ')
\end{code}

Also, every object in \G\ has a dual object.

\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
dual : ∀ {ℓ} {A B C D : Set ℓ} → R (A + D) (B + C) → R (D + A) (C + B)
dual f = r λ { (inl d) → (+-swap (fst (R-elim f (inr d)))) , (dual f)
             ; (inr a) → (+-swap (fst (R-elim f (inl a)))) , (dual f)
             }

dualize : ∀ {ℓ} {A B C D : Set ℓ} → G A B C D → G D C B A
dualize (g f) = g (dual f)
\end{code}

This makes \G\ a compact closed category.

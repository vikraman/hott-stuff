\AgdaHide{
\begin{code}
module GoI.Functions where

open import GoI.Base
\end{code}
}

The tensor product in \G\ is the exponential in linear logic. This means higher order functions in linear logic can be
encoded as compositions of resumptions.

\begin{code}
{-# NON_TERMINATING #-}
R-curry : ∀ {ℓ} {A B C D E F : Set ℓ}
        → R ((A + B) + F) ((C + D) + E) → R (A + (B + F)) (C + (D + E))
R-curry f' = r λ { (inl a) → +-assoc-l (fst (R-elim f' (inl (inl a)))) , R-curry f'
                 ; (inr (inl b)) → (+-assoc-l (fst (R-elim f' (inl (inr b))))) , (R-curry f')
                 ; (inr (inr f)) → (+-assoc-l (fst (R-elim f' (inr f)))) , (R-curry f')
                 }

G-curry : ∀ {ℓ} {A B C D E F : Set ℓ}
        → G (A + B) (C + D) E F → G A C (D + E) (B + F)
G-curry (g f) = g (R-curry f)

{-# NON_TERMINATING #-}
R-uncurry : ∀ {ℓ} {A B C D E F : Set ℓ}
          → R (A + (B + F)) (C + (D + E)) → R ((A + B) + F) ((C + D) + E)
R-uncurry f' = r λ { (inl (inl a)) → (+-assoc-r (fst (R-elim f' (inl a)))) , (R-uncurry f')
                   ; (inl (inr b)) → (+-assoc-r (fst (R-elim f' (inr (inl b))))) , (R-uncurry f')
                   ; (inr f) → (+-assoc-r (fst (R-elim f' (inr (inr f))))) , (R-uncurry f')
                   }

G-uncurry : ∀ {ℓ} {A B C D E F : Set ℓ}
          → G A C (D + E) (B + F) → G (A + B) (C + D) E F
G-uncurry (g f) = g (R-uncurry f)
\end{code}

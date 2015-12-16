\AgdaHide{
\begin{code}
module GoI.Functions where

open import GoI.Base
\end{code}
}

Morphisms in \G\ correspond to cut elimination in CMLL(Compact Multiplicative Linear Logic) which is equivalent to MLL
(Multiplicative Linear Logic) with \tensor\ and $A \multimap B = A^\bot \parr B$ such that,

\[
  (A^+, A^-) \multimap (B^+,B^-) = (A^+, A^-) \tensor (B^+, B^-)
\]

This means higher order functions in linear logic can be encoded as compositions of resumptions.

\[
  (A \multimap B) \multimap C \iso A \multimap (B \multimap C)
\]

\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
R-curry : ∀ {ℓ} {A A' B B' C C' : Set ℓ}
        → R ((A + A') + C') ((B + B') + C) → R (A + (A' + C')) (B + (B' + C))
R-curry f' = r λ { (inl a) → +-assoc-l (fst (R-elim f' (inl (inl a)))) , R-curry f'
                 ; (inr (inl a')) → (+-assoc-l (fst (R-elim f' (inl (inr a'))))) , (R-curry f')
                 ; (inr (inr c')) → (+-assoc-l (fst (R-elim f' (inr c')))) , (R-curry f')
                 }

G-curry : ∀ {ℓ} {A A' B B' C C' : Set ℓ}
        → G (A + A') (B + B') C C' → G A B (B' + C) (A' + C')
G-curry (g f) = g (R-curry f)
\end{code}
\AgdaHide{
\begin{code}
{-# NON_TERMINATING #-}
\end{code}
}
\begin{code}
R-uncurry : ∀ {ℓ} {A A' B B' C C' : Set ℓ}
          → R (A + (A' + C')) (B + (B' + C)) → R ((A + A') + C') ((B + B') + C)
R-uncurry f' = r λ { (inl (inl a)) → (+-assoc-r (fst (R-elim f' (inl a)))) , R-uncurry f'
                   ; (inl (inr a')) → (+-assoc-r (fst (R-elim f' (inr (inl a'))))) , R-uncurry f'
                   ; (inr c') → (+-assoc-r (fst (R-elim f' (inr (inr c'))))) , R-uncurry f'
                   }

G-uncurry : ∀ {ℓ} {A A' B B' C C' : Set ℓ}
          → G A B (B' + C) (A' + C') → G (A + A') (B + B') C C'
G-uncurry (g f) = g (R-uncurry f)
\end{code}

\AgdaHide{
\begin{code}
module GoI.Product where

open import GoI.Base
\end{code}
}
\AgdaHide{
\begin{code}
infixl 6 _***_
_***_ : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} {C D : Set ℓ₂} → R A B → R C D → R (A × C) (B × D)
idᵣ *** idᵣ = idᵣ
idᵣ *** r f = r λ { (a , c) → (a , fst (f c)) , idᵣ *** (snd (f c)) }
r f *** idᵣ = r λ { (a , c) → ((fst (f a)) , c) , snd (f a) *** idᵣ }
r f *** r f' = r λ { (a , c) → ((fst (f a)) , (fst (f' c))) , snd (f a) *** snd (f' c) }
\end{code}
}
\begin{code}

postulate R-swap : ∀ {ℓ} {A B : Set ℓ} → R A B → R B A

distrib : ∀ {ℓ} {A A' B B' C D : Set ℓ}
        → (((A' + B) × C) + ((A + B') × D))
        → ((B × C) + (A × D)) + ((A' × C) + (B' × D))
distrib (inl (inl a' , c)) = inr (inl (a' , c))
distrib (inl (inr b  , c)) = inl (inl (b , c))
distrib (inr (inl a  , d)) = inl (inr (a , d))
distrib (inr (inr b' , d)) = inr (inr (b' , d))

distrib' : ∀ {ℓ} {A' B' C D C' D' : Set ℓ}
         → ((A' × (C' + D)) + (B' × (C + D')))
         → ((B' × C) + (A' × D)) + ((A' × C') + (B' × D'))
distrib' (inl (a' , inl c')) = inr (inl (a' , c'))
distrib' (inl (a' , inr d )) = inl (inr (a' , d))
distrib' (inr (b' , inl c )) = inl (inl (b' , c))
distrib' (inr (b' , inr d')) = inr (inr (b' , d'))

{-# NON_TERMINATING #-}
R-distrib : ∀ {ℓ} {A A' B B' C D : Set ℓ}
          → R (((A + B') × C) + ((A' + B) × D)) (((A' + B) × C) + ((A + B') × D))
          → R (((A × C) + (B × D)) + ((B' × C) + (A' × D))) (((B × C) + (A × D)) + ((A' × C) + (B' × D)))
R-distrib f = r λ { (inl (inl (a  , c))) → distrib (fst (R-elim f (inl (inl a , c)))) , R-distrib f
                  ; (inl (inr (b  , d))) → distrib (fst (R-elim f (inr (inr b , d)))) , R-distrib f
                  ; (inr (inl (b' , c))) → distrib (fst (R-elim f (inl (inr b' , c)))) , R-distrib f
                  ; (inr (inr (a' , d))) → distrib (fst (R-elim f (inr (inl a' , d)))) , R-distrib f
                  }

{-# NON_TERMINATING #-}
R-distrib' : ∀ {ℓ} {A' B' C C' D D' : Set ℓ}
           → R ((A' × (C + D')) + (B' × (C' + D))) ((A' × (C' + D)) + (B' × (C + D')))
           → R (((A' × C) + (B' × D)) + ((B' × C') + (A' × D'))) (((B' × C) + (A' × D)) + ((A' × C') + (B' × D')))
R-distrib' f = r λ { (inl (inl (a' , c ))) → distrib' (fst (R-elim f (inl (a' , inl c)))) , R-distrib' f
                   ; (inl (inr (b' , d ))) → distrib' (fst (R-elim f (inr (b' , inr d)))) , R-distrib' f
                   ; (inr (inl (b' , c'))) → distrib' (fst (R-elim f (inr (b' , inl c')))) , R-distrib' f
                   ; (inr (inr (a' , d'))) → distrib' (fst (R-elim f (inl (a' , inr d')))) , R-distrib' f
                   }

{-# NON_TERMINATING #-}
extend : ∀ {ℓ} {A A' B B' C : Set ℓ}
       → R (A + B') (A' + B)
       → R ((A + B') × C) ((A' + B) × C)
extend f = r λ { (inl a , c) → ((fst (R-elim f (inl a))) , c) , extend f
               ; (inr b' , c) → ((fst (R-elim f (inr b'))) , c) , extend f
               }

{-# NON_TERMINATING #-}
extend' : ∀ {ℓ} {A A' B B' C : Set ℓ}
        → R (A + B') (A' + B)
        → R (C × (A + B')) (C × (A' + B))
extend' f = r λ { (c , inl a) → (c , (fst (R-elim f (inl a)))) , extend' f
                ; (c , inr b) → (c , (fst (R-elim f (inr b)))) , extend' f
                }

{-# NON_TERMINATING #-}
R-extend : ∀ {ℓ} {A A' B B' C D : Set ℓ}
         → R (A + B') (A' + B)
         → R (((A × C) + (B × D)) + ((B' × C) + (A' × D))) (((B × C) + (A × D)) + ((A' × C) + (B' × D)))
R-extend f = r λ e → fst (R-elim (R-distrib (extend f ** extend (R-swap f))) e) , R-extend f

G-extend : ∀ {ℓ} {A A' B B' C D : Set ℓ}
         → G A A' B B'
         → G ((A × C) + (B × D)) ((B × C) + (A × D)) ((A' × C) + (B' × D)) ((B' × C) + (A' × D))
G-extend (g f) = g (R-extend f)

{-# NON_TERMINATING #-}
R-extend' : ∀ {ℓ} {A' B' C C' D D' : Set ℓ}
          → R (C + D') (C' + D)
          → R (((A' × C) + (B' × D)) + ((B' × C') + (A' × D'))) (((B' × C) + (A' × D)) + ((A' × C') + (B' × D')))
R-extend' f = r λ e → fst (R-elim (R-distrib' (extend' f ** extend' (R-swap f))) e) , R-extend' f

G-extend' : ∀ {ℓ} {A' B' C C' D D' : Set ℓ}
          → G C C' D D'
          → G ((A' × C) + (B' × D)) ((B' × C) + (A' × D)) ((A' × C') + (B' × D')) ((B' × C') + (A' × D'))
G-extend' (g f) = g (R-extend' f)

G-combine : ∀ {ℓ} {A A' B B' C C' D D' : Set ℓ}
          → G A A' B B' → G C C' D D'
          → G ((A × C) + (B × D)) ((B × C) + (A × D)) ((A' × C') + (B' × D')) ((B' × C') + (A' × D'))
G-combine g₁ g₂ = G-extend g₁ >>> G-extend' g₂
\end{code}

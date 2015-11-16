module GoI.Product where

open import GoI.Base

infixl 6 _***_
_***_ : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} {C D : Set ℓ₂} → R A B → R C D → R (A × C) (B × D)
idᵣ *** idᵣ = idᵣ
idᵣ *** r f = r λ { (a , c) → (a , fst (f c)) , idᵣ *** (snd (f c)) }
r f *** idᵣ = r λ { (a , c) → ((fst (f a)) , c) , snd (f a) *** idᵣ }
r f *** r f' = r λ { (a , c) → ((fst (f a)) , (fst (f' c))) , snd (f a) *** snd (f' c) }

{-# NON_TERMINATING #-}
extend : ∀ {ℓ} {A A' B B' C : Set ℓ}
       → R (A + B') (A' + B)
       → R ((A + B') × C) ((A' + B) × C)
extend f = r λ { (inl a , c) → ((fst (R-elim f (inl a))) , c) , extend f
               ; (inr b , c) → ((fst (R-elim f (inr b))) , c) , extend f
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
R-extend f = r λ { (inl (inl (a , c))) → fst (R-elim (R-extend f) (inl (inl (a , c)))) , R-extend f
                 ; (inl (inr (b , d))) → fst (R-elim (R-extend f) (inl (inr (b , d)))) , R-extend f
                 ; (inr (inl (b' , c))) → fst (R-elim (R-extend f) (inr (inl (b' , c)))) , R-extend f
                 ; (inr (inr (a' , d))) → fst (R-elim (R-extend f) (inr (inr (a' , d)))) , R-extend f
                 }

G-extend : ∀ {ℓ} {A A' B B' C D : Set ℓ}
         → G A A' B B'
         → G ((A × C) + (B × D)) ((B × C) + (A × D)) ((A' × C) + (B' × D)) ((B' × C) + (A' × D))
G-extend (g f) = g (R-extend f)

{-# NON_TERMINATING #-}
R-extend' : ∀ {ℓ} {A' B' C C' D D' : Set ℓ}
          → R (C + D') (C' + D)
          → R (((A' × C) + (B' × D)) + ((B' × C') + (A' × D'))) (((B' × C) + (A' × D)) + ((A' × C') + (B' × D')))
R-extend' f' = r λ { (inl (inl (a' , c))) → fst (R-elim (R-extend' f') (inl (inl (a' , c)))) , R-extend' f'
                   ; (inl (inr (b' , d))) → fst (R-elim (R-extend' f') (inl (inr (b' , d)))) , R-extend' f'
                   ; (inr (inl (b' , c'))) → fst (R-elim (R-extend' f') (inr (inl (b' , c')))) , R-extend' f'
                   ; (inr (inr (a' , d'))) → fst (R-elim (R-extend' f') (inr (inr (a' , d')))) , R-extend' f'
                   }

G-extend' : ∀ {ℓ} {A' B' C C' D D' : Set ℓ}
          → G C C' D D'
          → G ((A' × C) + (B' × D)) ((B' × C) + (A' × D)) ((A' × C') + (B' × D')) ((B' × C') + (A' × D'))
G-extend' (g f) = g (R-extend' f)

G-combine : ∀ {ℓ} {A A' B B' C C' D D' : Set ℓ}
          → G A A' B B' → G C C' D D'
          → G ((A × C) + (B × D)) ((B × C) + (A × D)) ((A' × C') + (B' × D')) ((B' × C') + (A' × D'))
G-combine g₁ g₂ = G-extend g₁ >>> G-extend' g₂

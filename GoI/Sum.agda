module GoI.Sum where

open import GoI.Base

{-# NON_TERMINATING #-}
R-sym : ∀ {ℓ} {A B : Set ℓ} → R (A + B) (B + A)
R-sym = r λ { (inl a) → (inr a) , R-sym
            ; (inr b) → (inl b) , R-sym
            }

{-# NON_TERMINATING #-}
ρ : ∀ {ℓ} {A : Set ℓ} → R (A + ⊥) A
ρ = r λ { (inl a) → a , ρ
        ; (inr ⊥) → (⊥-elim ⊥) , ρ
        }

{-# NON_TERMINATING #-}
ρ' : ∀ {ℓ} {A : Set ℓ} → R A (A + ⊥)
ρ' = r λ { a → (inl a) , ρ' }

{-# NON_TERMINATING #-}
Λ : ∀ {ℓ} {A : Set ℓ} → R (⊥ + A) A
Λ = r λ { (inl ⊥) → (⊥-elim ⊥) , Λ
        ; (inr a) → a , Λ
        }

{-# NON_TERMINATING #-}
Λ' : ∀ {ℓ} {A : Set ℓ} → R A (⊥ + A)
Λ' = r λ { a → (inr a) , Λ' }

{-# NON_TERMINATING #-}
α : ∀ {ℓ} {A B C : Set ℓ} → R ((A + B) + C) (A + (B + C))
α = r λ { (inl (inl a)) → (inl a) , α
        ; (inl (inr b)) → (inr (inl b)) , α
        ; (inr b) → (inr (inr b)) , α
        }

{-# NON_TERMINATING #-}
α' : ∀ {ℓ} {A B C : Set ℓ} → R (A + (B + C)) ((A + B) + C)
α' = r λ { (inl a) → (inl (inl a)) , α'
         ; (inr (inl a)) → (inl (inr a)) , α'
         ; (inr (inr b)) → (inr b) , α'
         }

data G {ℓ} (A A' B B' : Set ℓ) : Set (suc ℓ) where
     g : R (A + B') (A' + B) → G A A' B B'

G-elim : ∀ {ℓ} {A A' B B' : Set ℓ} → G A A' B B' → R (A + B') (A' + B)
G-elim (g f) = f

id-G : ∀ {ℓ} {A B : Set ℓ} → G A B A B
id-G = g R-sym

{-# NON_TERMINATING #-}
assoc : ∀ {ℓ} {A B B' C' : Set ℓ} → R ((A + C') + (B' + B)) ((A + B') + (B + C'))
assoc = r λ { (inl (inl a)) → (inl (inl a)) , assoc
            ; (inl (inr b)) → (inr (inr b)) , assoc
            ; (inr (inl a)) → (inl (inr a)) , assoc
            ; (inr (inr b)) → (inr (inl b)) , assoc
            }

{-# NON_TERMINATING #-}
assoc' : ∀ {ℓ} {A' B B' C : Set ℓ} → R ((A' + B) + (B' + C)) ((A' + C) + (B' + B))
assoc' = r λ { (inl (inl a)) → (inl (inl a)) , assoc'
             ; (inl (inr b)) → (inr (inr b)) , assoc'
             ; (inr (inl a)) → (inr (inl a)) , assoc'
             ; (inr (inr b)) → (inl (inr b)) , assoc'
             }

infixl 4 _>>>_
_>>>_ : ∀ {ℓ} {A B C D E F : Set ℓ} → G A B C D → G C D E F → G A B E F
g f' >>> g g' = g (trace (assoc >> f' ** g' >> assoc'))

{-# NON_TERMINATING #-}
β : ∀ {ℓ} {A B C D : Set ℓ} → R ((A + B) + (C + D)) ((A + C) + (B + D))
β = r λ { (inl (inl a)) → (inl (inl a)) , β
        ; (inl (inr b)) → (inr (inl b)) , β
        ; (inr (inl a)) → (inl (inr a)) , β
        ; (inr (inr b)) → (inr (inr b)) , β
        }

{-# NON_TERMINATING #-}
β' : ∀ {ℓ} {A B C D : Set ℓ} → R ((A + C) + (B + D)) ((A + B) + (C + D))
β' = r λ { (inl (inl a)) → (inl (inl a)) , β'
         ; (inl (inr b)) → (inr (inl b)) , β'
         ; (inr (inl a)) → (inl (inr a)) , β'
         ; (inr (inr b)) → (inr (inr b)) , β'
         }

infixl 3 _++_
_++_ : ∀ {ℓ} {A' B' C' D' E' F' G' H' : Set ℓ}
     → G A' B' C' D' → G E' F' G' H' → G (A' + E') (B' + F') (C' + G') (D' + H')
g f' ++ g g' = g (β >> f' ** g' >> β')

{-# NON_TERMINATING #-}
dual : ∀ {ℓ} {A B C D : Set ℓ} → R (A + D) (B + C) → R (D + A) (C + B)
dual f = r λ { (inl d) → (+-swap (fst (R-elim f (inr d)))) , (dual f)
             ; (inr a) → (+-swap (fst (R-elim f (inl a)))) , (dual f)
             }

dualize : ∀ {ℓ} {A B C D : Set ℓ} → G A B C D → G D C B A
dualize (g f) = g (dual f)

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

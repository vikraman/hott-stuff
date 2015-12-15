\begin{code}
module GoI.Sum where

open import GoI.Base

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
\end{code}
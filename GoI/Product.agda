module GoI.Product where

open import GoI.Base

infixl 6 _***_
{-# NON_TERMINATING #-}
_***_ : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} {C D : Set ℓ₂} → R A B → R C D → R (A × C) (B × D)
idᵣ *** idᵣ = idᵣ
idᵣ *** r g = r λ { (a , c) → (a , fst (g c)) , idᵣ *** (snd (g c)) }
r f *** idᵣ = r λ { (a , c) → ((fst (f a)) , c) , snd (f a) *** idᵣ }
r f *** r g = r λ { (a , c) → ((fst (f a)) , (fst (g c))) , snd (f a) *** snd (g c) }

{-# NON_TERMINATING #-}
R-sym : ∀ {ℓ} {A B : Set ℓ} → R (A × B) (B × A)
R-sym = r λ { (a , b) → (b , a) , R-sym }

data G {ℓ} (A A' B B' : Set ℓ) : Set (suc ℓ) where
     g : R (A × B') (A' × B) → G A A' B B'

G-elim : ∀ {ℓ} {A A' B B' : Set ℓ} → G A A' B B' → R (A × B') (A' × B)
G-elim (g f) = f

id-G : ∀ {ℓ} {A B : Set ℓ} → G A B A B
id-G = g R-sym

{-# NON_TERMINATING #-}
assoc : ∀ {ℓ} {A B B' C' : Set ℓ} → R ((A × C') × (B' × B)) ((A × B') × (B × C'))
assoc = r λ { ((a , c') , (b' , b)) → ((a , b') , (b , c')) , assoc }

{-# NON_TERMINATING #-}
assoc' : ∀ {ℓ} {A' B B' C : Set ℓ} → R ((A' × B) × (B' × C)) ((A' × C) × (B' × B))
assoc' = r λ { ((a' , b) , (b' , c)) → ((a' , c) , (b' , b)) , assoc' }

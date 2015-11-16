module GoI.Base where

open import GoI.Types public

data R {ℓ} (i : Set ℓ) : Set ℓ → Set (suc ℓ) where
     idᵣ : R i i
     r  : {o : Set ℓ} → (i → (o × R i o)) → R i o

R-elim : ∀ {ℓ} {i o : Set ℓ} → R i o → i → (o × R i o)
R-elim idᵣ x = x , idᵣ
R-elim (r f) v = f v

id-R : ∀ {ℓ} {A : Set ℓ} → R A A
id-R {ℓ} {A} = idᵣ

infixl 5 _>>_
_>>_ : ∀ {ℓ} {A B C : Set ℓ} → R A B → R B C → R A C
f >> idᵣ = f
idᵣ >> g = g
r f >> r g = r (λ a → fst (g (fst (f a))) , snd (f a) >> snd (g (fst (f a))))

infixl 6 _**_
{-# NON_TERMINATING #-}
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

trace : ∀ {ℓ} {A B C : Set ℓ} → R (A + B) (C + B) → R A C
{-# NON_TERMINATING #-}
loop : ∀ {ℓ} {A B C : Set ℓ} → R (A + B) (C + B) → A + B → C × R A C
trace f = r (λ a → loop f (inl a))
loop f v with R-elim f v
... | inl c , f' = c , trace f'
... | inr b , f' = loop f' (inr b)

data G {ℓ} (A A' B B' : Set ℓ) : Set (suc ℓ) where
     g : R (A + B') (A' + B) → G A A' B B'

G-elim : ∀ {ℓ} {A A' B B' : Set ℓ} → G A A' B B' → R (A + B') (A' + B)
G-elim (g f) = f

{-# NON_TERMINATING #-}
R-sym : ∀ {ℓ} {A B : Set ℓ} → R (A + B) (B + A)
R-sym = r λ { (inl a) → (inr a) , R-sym
            ; (inr b) → (inl b) , R-sym
            }

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

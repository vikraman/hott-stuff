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

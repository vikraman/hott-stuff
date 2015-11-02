module GoI.Sum where

open import Level

open import Data.Unit
open import Data.Empty

infixr 4 _,_
infixr 2 _×_

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

×-swap : ∀ {a b} {A : Set a} {B : Set b} → A × B → B × A
×-swap (fst , snd) = snd , fst

infix 5 _+_

data _+_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
     inl : (a : A) → A + B
     inr : (b : B) → A + B

+-swap : ∀ {a b} {A : Set a} {B : Set b} → A + B → B + A
+-swap (inl a) = inr a
+-swap (inr b) = inl b

+-assoc-l : ∀ {a b c} {A : Set a} {B : Set b} { C : Set c}
          → (A + B) + C → A + (B + C)
+-assoc-l (inl (inl a)) = inl a
+-assoc-l (inl (inr b)) = inr (inl b)
+-assoc-l (inr c) = inr (inr c)

+-assoc-r : ∀ {a b c} {A : Set a} {B : Set b} { C : Set c}
          → A + (B + C) → (A + B) + C
+-assoc-r (inl a) = inl (inl a)
+-assoc-r (inr (inl b)) = inl (inr b)
+-assoc-r (inr (inr c)) = inr c

data R {ℓ} (i : Set ℓ) : Set ℓ → Set (suc ℓ) where
     idᵣ : R i i
     r  : {o : Set ℓ} → (i → (o × R i o)) → R i o
     -- r' : {o : Set ℓ} → (o → (i × R o i)) → R i o

R-elim : ∀ {ℓ} {i o : Set ℓ} → R i o → i → (o × R i o)
R-elim idᵣ x = x , idᵣ
R-elim (r f) v = f v

id-R : ∀ {ℓ} {A : Set ℓ} → R A A
id-R {ℓ} {A} = idᵣ

_>>_ : ∀ {ℓ} {A B C : Set ℓ} → R A B → R B C → R A C
f >> idᵣ = f
idᵣ >> g = g
r f >> r g = r (λ a → fst (g (fst (f a))) , snd (f a) >> snd (g (fst (f a))))

infixl 5 _>>_

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
infixl 6 _**_

trace : ∀ {ℓ} {A B C : Set ℓ} → R (A + B) (C + B) → R A C
{-# NON_TERMINATING #-}
loop : ∀ {ℓ} {A B C : Set ℓ} → R (A + B) (C + B) → A + B → C × R A C
trace f = r (λ a → loop f (inl a))
loop f v with R-elim f v
... | inl c , f' = c , trace f'
... | inr b , f' = loop f' (inr b)

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

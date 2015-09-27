module GoI where

open import Level

open import Data.Product
open import Data.Unit
open import Data.Sum
open import Data.Empty

data R {ℓ₁ ℓ₂} : Set ℓ₁ → Set ℓ₂ → Set (suc (ℓ₁ ⊔ ℓ₂)) where
     r : {i : Set ℓ₁} {o : Set ℓ₂} → i → (o × R i o) → R i o

{-# NON_TERMINATING #-}
id : ∀ {ℓ} {A : Set ℓ} {a : A} → R A A
id {ℓ} {A} {a} = r a (a , id {ℓ} {A} {a})

_>>_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
     → R A B → R B C → R A C
r x (y , f') >> r z (w , g') = r x (w , f' >> g')

_**_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {D : Set ℓ₄}
     → R A B → R C D → R (A ⊎ C) (B ⊎ D)
r x (y , f') ** r z (w , g') = r (inj₁ x) (inj₁ y , f' ** g')

trace : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
      → R (A ⊎ B) (C ⊎ B) → R A C
trace (r (inj₁ x) (proj₁ , proj₂)) = r x ({!!} , {!!})
trace (r (inj₂ y) (proj₁ , proj₂)) = r {!!} ({!!} , {!!})

loop : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
     → R (A ⊎ B) (A ⊎ C) → A ⊎ B → C × R B C
loop (r x (inj₁ x₁ , f')) (inj₁ x₂) = proj₁ (loop f' x) , {!!}
loop (r x (inj₂ y , f')) (inj₁ x₁) = y , {!!}
loop (r x (y , f')) (inj₂ y₁) = proj₁ (loop f' x) , {!!}

{-# NON_TERMINATING #-}
R-sym : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {a : A} {b : B} → R (A ⊎ B) (B ⊎ A)
R-sym {ℓ₁} {ℓ₂} {A} {B} {a} {b} = r (inj₁ a) (inj₁ b , R-sym {ℓ₁} {ℓ₂} {A} {B} {a} {b})

{-# NON_TERMINATING #-}
ρ : ∀ {ℓ} {A : Set ℓ} {a : A} → R (A ⊎ ⊥) A
ρ {ℓ} {A} {a} = r (inj₁ a) (a , ρ {ℓ} {A} {a})

{-# NON_TERMINATING #-}
ρ' : ∀ {ℓ} {A : Set ℓ} {a : A} → R A (A ⊎ ⊥)
ρ' {ℓ} {A} {a} = r a (inj₁ a , ρ' {ℓ} {A} {a})

{-# NON_TERMINATING #-}
Λ : ∀ {ℓ} {A : Set ℓ} {a : A} → R (⊥ ⊎ A) A
Λ {ℓ} {A} {a} = r (inj₂ a) (a , Λ {ℓ} {A} {a})

{-# NON_TERMINATING #-}
Λ' : ∀ {ℓ} {A : Set ℓ} {a : A} → R A (⊥ ⊎ A)
Λ' {ℓ} {A} {a} = r a ((inj₂ a) , Λ' {ℓ} {A} {a})

{-# NON_TERMINATING #-}
α : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {a : A} {b : B} {c : C}
  → R ((A ⊎ B) ⊎ C) (A ⊎ (B ⊎ C))
α {ℓ₁} {ℓ₂} {ℓ₃} {A} {B} {C} {a} {b} {c} = r (inj₂ c) ((inj₁ a) , α {ℓ₁} {ℓ₂} {ℓ₃} {A} {B} {C} {a} {b} {c})

{-# NON_TERMINATING #-}
α' : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {a : A} {b : B} {c : C}
  → R (A ⊎ (B ⊎ C)) ((A ⊎ B) ⊎ C)
α' {ℓ₁} {ℓ₂} {ℓ₃} {A} {B} {C} {a} {b} {c} = r (inj₁ a) ((inj₂ c) , α' {ℓ₁} {ℓ₂} {ℓ₃} {A} {B} {C} {a} {b} {c})

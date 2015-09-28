module GoI where

open import Level

open import Data.Product
open import Data.Unit
open import Data.Sum
open import Data.Empty

data R {ℓ} (i : Set ℓ) : Set ℓ → Set (suc ℓ) where
     idᵣ : R i i
     r : {o : Set ℓ} → i → (o × R i o) → R i o

R-elim : ∀ {ℓ} {i o : Set ℓ} → R i o → i → (o × R i o)
R-elim idᵣ x = x , idᵣ
R-elim (r x (y , f')) v = y , f'

id-R : ∀ {ℓ} {A : Set ℓ} → R A A
id-R {ℓ} {A} = idᵣ

_>>_ : ∀ {ℓ} {A B C : Set ℓ} → R A B → R B C → R A C
f >> idᵣ = f
idᵣ >> g = g
r x (y , f') >> r z (w , g') = f' >> g'

infixl 5 _>>_

_**_ : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} {C D : Set ℓ₂} → R A B → R C D → R (A ⊎ C) (B ⊎ D)
idᵣ ** idᵣ = idᵣ
idᵣ ** r x (y , f') = r (inj₂ x) ((inj₂ y) , idᵣ ** f')
r x (y , f') ** idᵣ = r (inj₁ x) ((inj₁ y) , (f' ** idᵣ))
r x (y , f') ** r z (w , g') = r (inj₁ x) (inj₁ y , f' ** g')

infixl 6 _**_

trace : ∀ {ℓ} {A B C : Set ℓ} {a : A} → R (A ⊎ B) (C ⊎ B) → R A C
{-# NON_TERMINATING #-}
loop : ∀ {ℓ} {A B C : Set ℓ} {a : A} → R (A ⊎ B) (C ⊎ B) → A ⊎ B → C × R A C
trace {a = a} f = r a (loop {a = a} f (inj₁ a))
loop f v with R-elim f v
loop {a = a} f v | inj₁ x , f' = x , trace {a = a} f'
loop {a = a} f v | inj₂ y , f' = loop {a = a} f' (inj₂ y)

{-# NON_TERMINATING #-}
R-sym : ∀ {ℓ} {A B : Set ℓ} {ab : A ⊎ B} → R (A ⊎ B) (B ⊎ A)
R-sym {ab = inj₁ a} = r (inj₁ a) ((inj₂ a) , R-sym {ab = inj₁ a})
R-sym {ab = inj₂ b} = r (inj₂ b) ((inj₁ b) , R-sym {ab = inj₂ b})

{-# NON_TERMINATING #-}
ρ : ∀ {ℓ} {A : Set ℓ} {ab : A ⊎ ⊥} → R (A ⊎ ⊥) A
ρ {ab = inj₁ a} = r (inj₁ a) (a , ρ {ab = inj₁ a})
ρ {ab = inj₂ b} = r (inj₂ b) (⊥-elim b , ρ {ab = inj₂ b})

{-# NON_TERMINATING #-}
ρ' : ∀ {ℓ} {A : Set ℓ} {a : A} → R A (A ⊎ ⊥)
ρ' {a = a} = r a ((inj₁ a) , ρ' {a = a})

{-# NON_TERMINATING #-}
Λ : ∀ {ℓ} {A : Set ℓ} {ab : ⊥ ⊎ A} → R (⊥ ⊎ A) A
Λ {ab = inj₁ a} = r (inj₁ a) ((⊥-elim a) , Λ {ab = inj₁ a})
Λ {ab = inj₂ b} = r (inj₂ b) (b , Λ {ab = inj₂ b})

{-# NON_TERMINATING #-}
Λ' : ∀ {ℓ} {A : Set ℓ} {a : A} → R A (⊥ ⊎ A)
Λ' {a = a} = r a ((inj₂ a) , Λ' {a = a})

{-# NON_TERMINATING #-}
α : ∀ {ℓ} {A B C : Set ℓ} {abc : ((A ⊎ B) ⊎ C)} → R ((A ⊎ B) ⊎ C) (A ⊎ (B ⊎ C))
α {abc = inj₁ (inj₁ a)} = r (inj₁ (inj₁ a)) ((inj₁ a) , α {abc = inj₁ (inj₁ a)})
α {abc = inj₁ (inj₂ b)} = r (inj₁ (inj₂ b)) ((inj₂ (inj₁ b)) , (α {abc = inj₁ (inj₂ b)}))
α {abc = inj₂ c} = r (inj₂ c) ((inj₂ (inj₂ c)) , α {abc = inj₂ c})

{-# NON_TERMINATING #-}
α' : ∀ {ℓ} {A B C : Set ℓ} {abc : (A ⊎ (B ⊎ C))} → R (A ⊎ (B ⊎ C)) ((A ⊎ B) ⊎ C)
α' {abc = inj₁ a} = r (inj₁ a) ((inj₁ (inj₁ a)) , α' {abc = inj₁ a})
α' {abc = inj₂ (inj₁ b)} = r (inj₂ (inj₁ b)) ((inj₁ (inj₂ b)) , (α' {abc = inj₂ (inj₁ b)}))
α' {abc = inj₂ (inj₂ c)} = r (inj₂ (inj₂ c)) ((inj₂ c) , (α' {abc = inj₂ (inj₂ c)}))

data G {ℓ} (A⁺ A⁻ B⁺ B⁻ : Set ℓ) : Set (suc ℓ) where
     g : R (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺) → G A⁺ A⁻ B⁺ B⁻

id-G : ∀ {ℓ} {A : Set ℓ} → G A A A A
id-G {ℓ} {A} = g id-R

{-# NON_TERMINATING #-}
assoc : ∀ {ℓ} {A⁺ B⁺ B⁻ C⁻ : Set ℓ} {e : ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺))}
      → R ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺)) ((A⁺ ⊎ B⁻) ⊎ (B⁺ ⊎ C⁻))
assoc {e = inj₁ (inj₁ a⁺)} = r (inj₁ (inj₁ a⁺)) ((inj₁ (inj₁ a⁺)) , assoc {e = inj₁ (inj₁ a⁺)})
assoc {e = inj₁ (inj₂ c⁻)} = r (inj₁ (inj₂ c⁻)) ((inj₂ (inj₂ c⁻)) , assoc {e = inj₁ (inj₂ c⁻)})
assoc {e = inj₂ (inj₁ b⁻)} = r (inj₂ (inj₁ b⁻)) ((inj₁ (inj₂ b⁻)) , assoc {e = inj₂ (inj₁ b⁻)})
assoc {e = inj₂ (inj₂ b⁺)} = r (inj₂ (inj₂ b⁺)) ((inj₂ (inj₁ b⁺)) , assoc {e = inj₂ (inj₂ b⁺)})

{-# NON_TERMINATING #-}
assoc2 : ∀ {ℓ} {A⁻ B⁺ B⁻ C⁺ : Set ℓ} {e : ((A⁻ ⊎ B⁺) ⊎ (B⁻ ⊎ C⁺))}
       → R ((A⁻ ⊎ B⁺) ⊎ (B⁻ ⊎ C⁺)) ((A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺))
assoc2 {e = inj₁ (inj₁ a⁻)} = r (inj₁ (inj₁ a⁻)) ((inj₁ (inj₁ a⁻)) , assoc2 {e = inj₁ (inj₁ a⁻)})
assoc2 {e = inj₁ (inj₂ b⁺)} = r (inj₁ (inj₂ b⁺)) ((inj₂ (inj₂ b⁺)) , assoc2 {e = inj₁ (inj₂ b⁺)})
assoc2 {e = inj₂ (inj₁ b⁻)} = r (inj₂ (inj₁ b⁻)) ((inj₂ (inj₁ b⁻)) , assoc2 {e = inj₂ (inj₁ b⁻)})
assoc2 {e = inj₂ (inj₂ c⁺)} = r (inj₂ (inj₂ c⁺)) ((inj₁ (inj₂ c⁺)) , assoc2 {e = inj₂ (inj₂ c⁺)})

_>>>_ : ∀ {ℓ} {A B C D E F : Set ℓ} → G A B C D → G C D E F → G A B E F
(g f') >>> (g g') = g (trace {a = {!!}} (assoc {e = {!!}} >> f' ** g' >> assoc2 {e = {!!}}))

infixl 4 _>>>_

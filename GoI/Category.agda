module GoI.Category where

open import GoI.Types
open import GoI.Base hiding (g)
open import GoI.Product

record Category (o ℓ : Level) : Set (suc (o ⊔ ℓ)) where
  infixr 9 _∘_
  field
    obj : Set o
    hom : obj → obj → Set ℓ
    id  : {a : obj} → hom a a
    _∘_ : {a b c : obj} → hom b c → hom a b → hom a c

  op : Category o ℓ
  op = record { obj = obj
              ; hom = λ a b → hom b a
              ; id = id
              ; _∘_ = λ g f → f ∘ g
              }

record Functor {o o' ℓ ℓ' : Level} (C : Category o ℓ) (D : Category o' ℓ') : Set (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
  private module C = Category C
  private module D = Category D
  field
    Fobj : C.obj → D.obj
    Fhom : {a b : C.obj} → C.hom a b → D.hom (Fobj a) (Fobj b)

module Product where
  open Category
  _*_ : ∀ {o o' ℓ ℓ'} → Category o ℓ → Category o' ℓ' → Category (o ⊔ o') (ℓ ⊔ ℓ')
  C * D = record { obj = obj C × obj D
                 ; hom = λ { (ca , da) (cb , db) → hom C ca cb × hom D da db }
                 ; id = λ { {c , d} → id C {c} , id D {d} }
                 ; _∘_ = λ { (fc , gc) (fd , gd) → (_∘_ C fc fd) , (_∘_ D gc gd) }
                 }

record Monoidal (o ℓ : Level) (C : Category o ℓ) : Set (o ⊔ ℓ) where
  private module C = Category C
  open C
  open Product
  field
    ⊗ : Functor (C * C) C
    𝟙 : obj
  private module F = Functor ⊗
  open F
  infixr 9 _⊗_
  _⊗_ : obj → obj → obj
  _⊗_ = λ a b → Fobj (a , b)

record Traced (o ℓ : Level) (C : Category o ℓ) (M : Monoidal o ℓ C) : Set (o ⊔ ℓ) where
  private module C = Category C
  open C
  private module M = Monoidal M
  open M hiding (⊗)
  field
    tr : ∀ {a b c : obj} → hom (a ⊗ c) (b ⊗ c) → hom a b

record Compact (o ℓ : Level) (C : Category o ℓ) (M : Monoidal o ℓ C) : Set (o ⊔ ℓ) where
  private module C = Category C
  open C
  private module M = Monoidal M
  open M hiding (⊗)
  infixr 9 _*
  field
    _* : obj → obj

Ⓡ : ∀ {ℓ} → Category (suc ℓ) (suc ℓ)
Ⓡ {ℓ} = record { obj = Set ℓ
                ; hom = λ i o → R i o
                ; id  = idᵣ
                ; _∘_ = λ g f → f >> g
                }

Ⓡ-+ : ∀ {ℓ} → Monoidal (suc ℓ) (suc ℓ) Ⓡ
Ⓡ-+ = record { ⊗ = record { Fobj = λ { (a , b) → a + b }
                           ; Fhom = λ { (f , g) → f ** g }
                           }
              ; 𝟙 = ⊥
              }

Ⓡ-+-trace : ∀ {ℓ} → Traced (suc ℓ) (suc ℓ) Ⓡ Ⓡ-+
Ⓡ-+-trace = record { tr = trace }

Ⓡ-× : ∀ {ℓ} → Monoidal (suc ℓ) (suc ℓ) Ⓡ
Ⓡ-× = record { ⊗ = record { Fobj = λ { (a , b) → a × b }
                           ; Fhom = λ { (f , g) → f *** g }
                           }
              ; 𝟙 = ⊤
              }

Ⓖ : ∀ {ℓ} → Category (suc ℓ) (suc ℓ)
Ⓖ {ℓ} = record { obj = Set ℓ × Set ℓ
                ; hom = λ { (a , a') (b , b') → G a a' b b' }
                ; id = id-G
                ; _∘_ = λ g f → f >>> g
                }

Ⓖ-+ : ∀ {ℓ} → Monoidal (suc ℓ) (suc ℓ) Ⓖ
Ⓖ-+ = record { ⊗ = record { Fobj = λ { ((a , a') , (b , b')) → (a + b) , (a' + b') }
                           ; Fhom = λ { (f , h) → f ++ h }
                           }
              ; 𝟙 = ⊥ , ⊥
              }

Ⓖ-+-compact : ∀ {ℓ} → Compact (suc ℓ) (suc ℓ) Ⓖ Ⓖ-+
Ⓖ-+-compact = record { _* = λ { (a , a') → (a' , a) } }

postulate _××_ : ∀ {ℓ} {A A' B B' C C' D D' : Set ℓ}
               → G A A' B B' → G C C' D D'
               → G (A × C + A' × C') (A × C' + A' × C)
                   (B × D + B' × D') (B × D' + B' × D)

Ⓖ-× : ∀ {ℓ} → Monoidal (suc ℓ) (suc ℓ) Ⓖ
Ⓖ-× = record { ⊗ = record { Fobj = λ { ((a , a') , (b , b')) → (a × b + a' × b') , (a × b' + a' × b) }
                           ; Fhom = λ { (f , h) → f ×× h }
                           }
              ; 𝟙 = ⊥ , ⊥
              }

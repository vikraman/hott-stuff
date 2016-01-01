module GoI.Trace where

open import GoI.Base hiding (trace)

module TraceProduct where
  postulate trace : ∀ {ℓ} {A B C : Set ℓ} → R (A × C) (B × C) → R A B

  foo : ∀ {ℓ} {A B : Set ℓ} → R A B → A → B
  foo f a with R-elim f a
  ... | b , f' = b

  {-# NON_TERMINATING #-}
  bar : ∀ {ℓ} {A B : Set ℓ} → R (A × ⊥ {ℓ}) (B × ⊥ {ℓ})
  bar = r λ { (a , ⊥) → ⊥-elim ⊥ , bar }

  baz : ∀ {ℓ} {A B : Set ℓ} → A → B
  baz = foo (trace bar)

  false : ∀ {ℓ} → ⊥ {ℓ}
  false = baz ⊤⊤

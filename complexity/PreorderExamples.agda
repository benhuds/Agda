open import Preliminaries
open import Preorder

module PreorderExamples where

-- there is a preorder on Unit

  unit-p : Preorder Unit
  unit-p = preorder (preorder-structure (λ x x₁ → Unit) (λ x → <>) (λ x y z _ _ → <>))

-- there is a preorder on Nat

  _≤n_ : Nat → Nat → Set
  _≤n_ Z Z = Unit
  _≤n_ Z (S n) = Unit
  _≤n_ (S m) Z = Void
  _≤n_ (S m) (S n) = m ≤n n

  nat-refl : ∀ (n : Nat) → n ≤n n
  nat-refl Z = <>
  nat-refl (S n) = nat-refl n

  nat-trans : ∀ (m n p : Nat) → m ≤n n → n ≤n p → m ≤n p
  nat-trans Z Z Z x x₁ = <>
  nat-trans Z Z (S p) x x₁ = <>
  nat-trans Z (S n) Z x x₁ = <>
  nat-trans Z (S n) (S p) x x₁ = <>
  nat-trans (S m) Z Z () x₁
  nat-trans (S m) Z (S p) () x₁
  nat-trans (S m) (S n) Z x ()
  nat-trans (S m) (S n) (S p) x x₁ = nat-trans m n p x x₁

  nat-p : Preorder Nat
  nat-p = preorder (preorder-structure (λ m n → m ≤n n) nat-refl nat-trans)

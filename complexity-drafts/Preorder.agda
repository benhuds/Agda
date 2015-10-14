open import Preliminaries

module Preorder where

  record PreorderStructure (A : Set) : Set1 where
    constructor preorder-structure
    field
      _≤_ : A → A → Set
      refl : ∀ x → x ≤ x
      trans : ∀ x y z → x ≤ y → y ≤ z → x ≤ z

  record Preorder A : Set1 where
    constructor preorder
    field
      preorder-struct : PreorderStructure A

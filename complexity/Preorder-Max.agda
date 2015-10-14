{- Name: Bowornmet (Ben) Hudson

--Preorders 2: Electric Boogaloo--

-}

open import Preliminaries

module Preorder-Max where

  {- Doing the same thing as we did in Preorder.agda but this
     time we want to keep our end goal in mind and extend the
     notion of preorders to include information about maximums
     as well. This will make it easier to 'ensure' that functions
     on nats are monotone (because they sometimes aren't - e.g.
     sine, cosine, etc.) so we can give them a reasonable upper bound.
     If we don't monotonize functions on nats then that makes bounding
     more complicated. This also means we have to extend the idea of
     maximums to all our other types...
  -}
  record Preorder-max-str (A : Set) : Set1 where
    constructor preorder-max
    field
      ≤ : A → A → Set
      refl : ∀ x → ≤ x x
      trans : ∀ x y z → ≤ x y → ≤ y z → ≤ x z
      max : A → A → A
      max-l : ∀ l r → ≤ l (max l r)
      max-r : ∀ l r → ≤ r (max l r)
      max-lub : ∀ k l r → ≤ l k → ≤ r k → ≤ (max l r) k

------------------------------------------

  -- order on nats
  ≤nat : Nat → Nat → Set
  ≤nat Z Z = Unit
  ≤nat Z (S y) = Unit
  ≤nat (S x) Z = Void
  ≤nat (S x) (S y) = ≤nat x y

  -- proof that Nat is reflexive under ≤
  nat-refl : ∀ (x : Nat) → ≤nat x x
  nat-refl Z = <>
  nat-refl (S x) = nat-refl x

  -- proof that Nat is transitive under ≤
  nat-trans : ∀ (x y z : Nat) → ≤nat x y → ≤nat y z → ≤nat x z
  nat-trans Z Z Z p q = <>
  nat-trans Z Z (S z) p q = <>
  nat-trans Z (S y) Z p q = <>
  nat-trans Z (S y) (S z) p q = <>
  nat-trans (S x) Z Z p q = p
  nat-trans (S x) Z (S z) () q
  nat-trans (S x) (S y) Z p ()
  nat-trans (S x) (S y) (S z) p q = nat-trans x y z p q

  -- nat max
  nat-max : Nat → Nat → Nat
  nat-max Z n = n
  nat-max (S m) Z = S m
  nat-max (S m) (S n) = S (nat-max m n)

  -- left max
  nat-max-l : ∀ (l r : Nat) → ≤nat l (nat-max l r)
  nat-max-l Z Z = <>
  nat-max-l Z (S n) = <>
  nat-max-l (S m) Z = nat-refl m
  nat-max-l (S m) (S n) = nat-max-l m n

  -- right max
  nat-max-r : ∀ (l r : Nat) → ≤nat r (nat-max l r)
  nat-max-r Z Z = <>
  nat-max-r Z (S n) = nat-refl n
  nat-max-r (S m) Z = <>
  nat-max-r (S m) (S n) = nat-max-r m n

  -- rub a dub dub, Nats have a lub
  nat-max-lub : ∀ (k l r : Nat) → ≤nat l k → ≤nat r k → ≤nat (nat-max l r) k
  nat-max-lub Z Z Z p q = <>
  nat-max-lub Z Z (S r) p ()
  nat-max-lub Z (S l) Z () q
  nat-max-lub Z (S l) (S r) () q
  nat-max-lub (S k) Z Z p q = <>
  nat-max-lub (S k) Z (S r) p q = q
  nat-max-lub (S k) (S l) Z p q = p
  nat-max-lub (S k) (S l) (S r) p q = nat-max-lub k l r p q

  -- Nat is preorder with max
  nat-p : Preorder-max-str Nat
  nat-p = preorder-max ≤nat nat-refl nat-trans nat-max nat-max-l nat-max-r nat-max-lub

------------------------------------------

--same thing for products

  -- relation for products
  ≤axb : ∀ {A B : Set} → Preorder-max-str A → Preorder-max-str B → (A × B) → (A × B) → Set
  ≤axb PA PB (a1 , b1) (a2 , b2) = Preorder-max-str.≤ PA a1 a2 × Preorder-max-str.≤ PB b1 b2

  axb-refl : ∀ {A B : Set} → (PA : Preorder-max-str A) → (PB : Preorder-max-str B) → (x : (A × B)) →  ≤axb PA PB x x
  axb-refl PA PB (a , b) = Preorder-max-str.refl PA a , Preorder-max-str.refl PB b

  axb-trans : ∀ {A B : Set} → (PA : Preorder-max-str A) → (PB : Preorder-max-str B) → (x y z : (A × B)) → ≤axb PA PB x y → ≤axb PA PB y z → ≤axb PA PB x z
  axb-trans PA PB (a1 , b1) (a2 , b2) (a3 , b3) (a1<a2 , b1<b2) (a2<a3 , b2<b3) = 
                          Preorder-max-str.trans PA a1 a2 a3 a1<a2 a2<a3 , Preorder-max-str.trans PB b1 b2 b3 b1<b2 b2<b3

  axb-max : ∀ {A B : Set} → Preorder-max-str A → Preorder-max-str B → (A × B) → (A × B) → (A × B)
  axb-max PA PB (a1 , b1) (a2 , b2) = Preorder-max-str.max PA a1 a2 , Preorder-max-str.max PB b1 b2

  axb-max-l : ∀ {A B : Set} → (PA : Preorder-max-str A) → (PB : Preorder-max-str B) → (l r : (A × B)) → ≤axb PA PB l (axb-max PA PB l r)
  axb-max-l PA PB (a1 , b1) (a2 , b2) = Preorder-max-str.max-l PA a1 a2 , Preorder-max-str.max-l PB b1 b2

  axb-max-r : ∀ {A B : Set} → (PA : Preorder-max-str A) → (PB : Preorder-max-str B) → (l r : (A × B)) → ≤axb PA PB r (axb-max PA PB l r)
  axb-max-r PA PB (a1 , b1) (a2 , b2) = Preorder-max-str.max-r PA a1 a2 , Preorder-max-str.max-r PB b1 b2

  axb-max-lub : ∀ {A B : Set} 
                → (PA : Preorder-max-str A) 
                → (PB : Preorder-max-str B) 
                → (k l r : (A × B)) 
                → ≤axb PA PB l k → ≤axb PA PB r k → ≤axb PA PB (axb-max PA PB l r) k
  axb-max-lub PA PB (k1 , k2) (l1 , l2) (r1 , r2) (l1<k1 , l2<k2) (r1<k1 , r2<k2) =
                 Preorder-max-str.max-lub PA k1 l1 r1 l1<k1 r1<k1 , Preorder-max-str.max-lub PB k2 l2 r2 l2<k2 r2<k2

  axb-p : ∀ (A B : Set) → Preorder-max-str A → Preorder-max-str B → Preorder-max-str (A × B)
  axb-p A B PA PB = preorder-max (≤axb PA PB) (axb-refl PA PB) (axb-trans PA PB) (axb-max PA PB) (axb-max-l PA PB) (axb-max-r PA PB) (axb-max-lub PA PB)

------------------------------------------

  -- the type of monotone functions from A to B
  record Monotone (A : Set) (B : Set) (PA : Preorder-max-str A) (PB : Preorder-max-str B) : Set where
    constructor monotone
    field
      f : A → B
      is-monotone : ∀ (x y : A) → Preorder-max-str.≤ PA x y → Preorder-max-str.≤ PB (f x) (f y)

  ≤mono : ∀ {A B : Set} → (PA : Preorder-max-str A) → (PB : Preorder-max-str B) → (Monotone A B PA PB) → (Monotone A B PA PB) → Set
  ≤mono {A} PA PB f g = (x : A) → Preorder-max-str.≤ PB (Monotone.f f x) (Monotone.f g x)

  mono-refl : ∀ {A B : Set} → (PA : Preorder-max-str A) → (PB : Preorder-max-str B) → (x : (Monotone A B PA PB)) → ≤mono PA PB x x
  mono-refl PA PB f = λ x → Preorder-max-str.refl PB (Monotone.f f x)

  mono-trans : ∀ {A B : Set} → (PA : Preorder-max-str A) → (PB : Preorder-max-str B) → (x y z : (Monotone A B PA PB)) → ≤mono PA PB x y → ≤mono PA PB y z → ≤mono PA PB x z
  mono-trans PA PB f g h p q = λ x → Preorder-max-str.trans PB (Monotone.f f x) (Monotone.f g x) (Monotone.f h x) (p x) (q x)

  mono-max : ∀ {A B : Set} → (PA : Preorder-max-str A) → (PB : Preorder-max-str B) → (Monotone A B PA PB) → (Monotone A B PA PB) → (Monotone A B PA PB)
  mono-max PA PB (monotone f f-ismono) (monotone g g-ismono) = 
             monotone (λ x → Preorder-max-str.max PB (f x) (g x)) (λ x y x₁ → Preorder-max-str.max-lub PB (Preorder-max-str.max PB (f y) (g y)) (f x) (g x) 
               (Preorder-max-str.trans PB (f x) (f y) (Preorder-max-str.max PB (f y) (g y)) (f-ismono x y x₁) (Preorder-max-str.max-l PB (f y) (g y))) 
                 (Preorder-max-str.trans PB (g x) (g y) (Preorder-max-str.max PB (f y) (g y)) (g-ismono x y x₁) (Preorder-max-str.max-r PB (f y) (g y))))

  mono-max-l : ∀ {A B : Set} → (PA : Preorder-max-str A) → (PB : Preorder-max-str B) → (l r : Monotone A B PA PB) → ≤mono PA PB l (mono-max PA PB l r)
  mono-max-l PA PB f g = λ x → Preorder-max-str.max-l PB (Monotone.f f x) (Monotone.f g x)

  mono-max-r : ∀ {A B : Set} → (PA : Preorder-max-str A) → (PB : Preorder-max-str B) → (l r : Monotone A B PA PB) → ≤mono PA PB r (mono-max PA PB l r)
  mono-max-r PA PB f g = λ x → Preorder-max-str.max-r PB (Monotone.f f x) (Monotone.f g x)

  mono-max-lub : ∀ {A B : Set} 
                → (PA : Preorder-max-str A) 
                → (PB : Preorder-max-str B) 
                → (k l r : Monotone A B PA PB) 
                → ≤mono PA PB l k → ≤mono PA PB r k → ≤mono PA PB (mono-max PA PB l r) k
  mono-max-lub PA PB f g h p q = λ x → Preorder-max-str.max-lub PB (Monotone.f f x) (Monotone.f g x) (Monotone.f h x) (p x) (q x)

  mono-p : ∀ (A B : Set) → (PA : Preorder-max-str A) → (PB : Preorder-max-str B) → Preorder-max-str (Monotone A B PA PB)
  mono-p A B PA PB = preorder-max (≤mono PA PB) (mono-refl PA PB) (mono-trans PA PB) (mono-max PA PB) (mono-max-l PA PB) (mono-max-r PA PB) (mono-max-lub PA PB)

------------------------------------------

--"Hey, let's make things monotone!"

  -- another way to define the ≤ relation on Nat
  data _≤'_ : Nat → Nat → Set where
    x≤'x : {x : Nat} → x ≤' x
    x≤'y : {x y : Nat} → x ≤' y → x ≤' (S y)

  -- silly lemmas about silly nats
  nat-lemma : (x : Nat) → Z ≤' x
  nat-lemma Z = x≤'x
  nat-lemma (S x) = x≤'y (nat-lemma x)

  nat-lemma2 : (x y : Nat) → x ≤' y → (S x) ≤' (S y)
  nat-lemma2 .y y x≤'x = x≤'x
  nat-lemma2 x .(S y) (x≤'y {.x} {y} p) = x≤'y (nat-lemma2 x y p)

  nat-lemma3 : (x : Nat) → ≤nat x (S x)
  nat-lemma3 Z = <>
  nat-lemma3 (S x) = nat-lemma3 x

  -- maps to and from the old and new definitions of the ≤ relation
  ≤-map : (x y : Nat) → ≤nat x y → x ≤' y
  ≤-map Z Z f = x≤'x
  ≤-map Z (S y) f = nat-lemma (S y)
  ≤-map (S x) Z ()
  ≤-map (S x) (S y) f = nat-lemma2 x y (≤-map x y f)

  ≤-map2 : (x y : Nat) → x ≤' y → ≤nat x y
  ≤-map2 .y y x≤'x = nat-refl y
  ≤-map2 x .(S y) (x≤'y {.x} {y} f) = nat-trans x y (S y) (≤-map2 x y f) (nat-lemma3 y)

  -- a function to find the maximum of a whole set and not just a pair of values
  max' : ∀ {A : Set} → (PA : Preorder-max-str A) → Nat → (Nat → A) → A
  max' PA Z f = f Z
  max' PA (S n) f = Preorder-max-str.max PA (f (S n)) (max' PA n f)

  -- primitive recursion function corresponding to rec
  natrec : ∀{C : Set} → C → (Nat → C → C) → Nat → C
  natrec base step Z = base
  natrec base step (S n) = step n (natrec base step n)

  -- another lemma
  mono-f-lemma : ∀ {A : Set} → (x y : Nat) → x ≤' y → (PA : Preorder-max-str A) → (f : Nat → A) → Preorder-max-str.≤ PA (max' PA x f) (max' PA y f)
  mono-f-lemma .y y x≤'x PA f = Preorder-max-str.refl PA (max' PA y f)
  mono-f-lemma x .(S y) (x≤'y {.x} {y} p) PA f = Preorder-max-str.trans PA (max' PA x f) (max' PA y f) (max' PA (S y) f)
                                                                        (mono-f-lemma x y p PA f) (Preorder-max-str.max-r PA (f (S y)) (max' PA y f))

  -- make a function monotone by taking the max at every point
  mono-f : ∀ {A : Set} → (PA : Preorder-max-str A) → (f : Nat → A) → Monotone Nat A nat-p PA
  mono-f PA f = monotone (λ x → max' PA x f) (λ x y x₁ → mono-f-lemma x y (≤-map x y x₁) PA f)

  -- f ≤ (monotonization of f)
  mono-f-is-monotone : ∀ {A : Set} → (PA : Preorder-max-str A) → (x : Nat) → (f : Nat → A) → Preorder-max-str.≤ PA (f x) (Monotone.f (mono-f PA f) x)
  mono-f-is-monotone PA Z f = Preorder-max-str.refl PA (f Z)
  mono-f-is-monotone PA (S x) f = Preorder-max-str.max-l PA (f (S x)) (max' PA x f)

  -- if f is already monotone, then its monotonization is less than or equal to itself
  mono-f-≤-itself : ∀ {A : Set}
                    → (PA : Preorder-max-str A)
                    → (x : Nat)
                    → (f : Monotone Nat A nat-p PA)
                    →  Preorder-max-str.≤ PA (Monotone.f (mono-f PA (Monotone.f f)) x) (Monotone.f f x)
  mono-f-≤-itself PA Z f = Preorder-max-str.refl PA (Monotone.f (mono-f PA (Monotone.f f)) Z)
  mono-f-≤-itself PA (S x) f = Preorder-max-str.max-lub PA (Monotone.f f (S x)) (Monotone.f f (S x)) (max' PA x (Monotone.f f)) 
                                                        (Preorder-max-str.refl PA (Monotone.f f (S x))) 
                                                          (Preorder-max-str.trans PA (max' PA x (Monotone.f f)) 
                                                            (Monotone.f f x) (Monotone.f f (S x)) (mono-f-≤-itself PA x f)
                                                              (Monotone.is-monotone f x (S x) (≤-map2 x (S x) (x≤'y x≤'x))))

  -- monotonize at the end
  mnatrec : ∀ {A : Set} → (PA : Preorder-max-str A) → A → (Nat → A → A) → Nat → A
  mnatrec PA zc sc e = max' PA e (natrec zc sc)

  -- still incorrect
  mono-natrec : ∀ {A : Set} → (PA : Preorder-max-str A) → A → (Nat → A → A) → Nat → A
  mono-natrec PA zc sc Z = zc
  mono-natrec PA zc sc (S y') = Preorder-max-str.max PA zc (sc y' (mono-natrec PA zc sc y'))

  data N' : Set where
    Z1 : N'
    Sa : N' → N'
    Sb : N' → N'



------------------------------------------

-- same thing as Preorder.agda but for this module

  PREORDER = Σ (λ (A : Set) → Preorder-max-str A)

  MONOTONE : (PΓ PA : PREORDER) → Set
  MONOTONE (Γ , PΓ) (A , PA) = Monotone Γ A PΓ PA

  -- some operations
  _×p_ : PREORDER → PREORDER → PREORDER
  (A , PA) ×p (B , PB) = A × B , axb-p A B PA PB

  _->p_ : PREORDER → PREORDER → PREORDER
  (A , PA) ->p (B , PB) = Monotone A B PA PB , mono-p A B PA PB

  -- Unit is a preorder
  unit-p : PREORDER
  unit-p = Unit , preorder-max (λ x x₁ → Unit) (λ x → <>) (λ x y z _ _ → <>) (λ _ _ → <>) (λ l r → <>) (λ l r → <>) (λ k l r _ _ → <>)

  -- identity preserves monotonicity
  id : ∀ {Γ} → MONOTONE Γ Γ
  id = λ {Γ} → monotone (λ x → x) (λ x y x₁ → x₁)

  -- composition preserves monotonicity
  comp : ∀ {PA PB PC} → MONOTONE PA PB → MONOTONE PB PC → MONOTONE PA PC
  comp (monotone f f-ismono) (monotone g g-ismono) = monotone (λ x → g (f x)) (λ x y x₁ → g-ismono (f x) (f y) (f-ismono x y x₁))

  -- proofs that types like pairs etc. with preorders are monotone
  pair' : ∀ {PΓ PA PB} → MONOTONE PΓ PA → MONOTONE PΓ PB → MONOTONE PΓ (PA ×p PB)
  pair' (monotone f f-ismono) (monotone g g-ismono) = monotone (λ x → (f x) , (g x)) (λ x y x₁ → f-ismono x y x₁ , g-ismono x y x₁)

  fst' : ∀ {PΓ PA PB} → MONOTONE PΓ (PA ×p PB) → MONOTONE PΓ PA
  fst' (monotone f f-ismono) = 
          monotone (λ x → fst (f x)) (λ x y z → fst (f-ismono x y z))

  snd' : ∀ {PΓ PA PB} → MONOTONE PΓ (PA ×p PB) → MONOTONE PΓ PB
  snd' (monotone f f-ismono) = 
          monotone (λ x → snd (f x)) (λ x y z → snd (f-ismono x y z))

  lam' : ∀ {PΓ PA PB} → MONOTONE (PΓ ×p PA) PB → MONOTONE PΓ (PA ->p PB)
  lam' {Γ , preorder-max _ reflΓ _ _ _ _ _} {A , preorder-max _ refla _ _ _ _ _} (monotone f f-ismono) =
          monotone (λ x → monotone (λ p → f (x , p)) (λ a b c → f-ismono (x , a) (x , b) ((reflΓ x) , c))) (λ x y z w → f-ismono (x , w) (y , w) (z , (refla w)))

  app' : ∀ {PΓ PA PB} → MONOTONE PΓ (PA ->p PB) → MONOTONE PΓ PA → MONOTONE PΓ PB
  app' {_} {_} {b , preorder-max _ _ transb _ _ _ _} (monotone f f-ismono) (monotone g g-ismono) =
          monotone (λ x → Monotone.f (f x) (g x)) (λ x y z → transb (Monotone.f (f x) (g x)) (Monotone.f (f y) (g x)) (Monotone.f (f y) (g y))
          (f-ismono x y z (g x)) (Monotone.is-monotone (f y) (g x) (g y) (g-ismono x y z)))

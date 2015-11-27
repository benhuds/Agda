{- PREORDERS WITH MAXIMUMS -}

open import Preliminaries

module Preorder-Max where

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

  record Pre-wtop (A : Set) : Set1 where
    constructor pt
    field
      ≤ : A → A → Set
      refl : ∀ x → ≤ x x
      trans : ∀ x y z → ≤ x y → ≤ y z → ≤ x z
      max : A → A → A
      max-l : ∀ l r → ≤ l (max l r)
      max-r : ∀ l r → ≤ r (max l r)
      max-lub : ∀ k l r → ≤ l k → ≤ r k → ≤ (max l r) k
      top : A
      top-max : ∀ x → ≤ x top

------------------------------------------

  en = Either Nat Unit

------------------------------------------

  -- NAT WITH ≤ RELATION
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

  -- primitive recursion function corresponding to rec
  natrec : ∀{C : Set} → (base : C) → (step : Nat → C → C) → (n : Nat) → C
  natrec base step Z = base
  natrec base step (S n) = step n (natrec base step n)

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

  PN : PREORDER
  PN = Nat , nat-p

  -- Unit is a preorder
  unit-p : PREORDER
  unit-p = Unit , preorder-max (λ x x₁ → Unit) (λ x → <>) (λ x y z _ _ → <>) (λ _ _ → <>) (λ l r → <>) (λ l r → <>) (λ k l r _ _ → <>)

  -- identity preserves monotonicity
  id : ∀ {Γ} → MONOTONE Γ Γ
  id = λ {Γ} → monotone (λ x → x) (λ x y x₁ → x₁)

  -- composition preserves monotonicity
  comp : ∀ {PA PB PC} → MONOTONE PA PB → MONOTONE PB PC → MONOTONE PA PC
  comp (monotone f f-ismono) (monotone g g-ismono) = monotone (λ x → g (f x)) (λ x y x₁ → g-ismono (f x) (f y) (f-ismono x y x₁))

--  plus' : ∀ {PΓ} → MONOTONE PΓ PN → MONOTONE PΓ PN → MONOTONE PΓ PN
--  plus' {fst , preorder-max ≤ refl trans max max-l max-r max-lub} (monotone f f-is-monotone) (monotone g g-is-monotone) = monotone (λ x → f x + g x) (λ x y x₁ → {!!})

  z' : ∀ {PΓ} → MONOTONE PΓ PN
  z' = monotone (λ x → Z) (λ x y x₁ → <>)

  suc' : ∀ {PΓ} → MONOTONE PΓ PN → MONOTONE PΓ PN
  suc' {fst , preorder-max ≤ refl trans max max-l max-r max-lub} (monotone f is-monotone) = monotone (λ x → S (f x)) (λ x y x₁ → is-monotone x y x₁)

  e0-lem : ∀ {PΓ PC} → (e0 : MONOTONE PΓ PC) → (e1 : MONOTONE (PΓ ×p (PN ×p PC)) PC) → (x y : fst (PΓ ×p PN)) --→ (k : fst PN)
         → (∀ x → Preorder-max-str.≤ (snd PC) (Monotone.f e0 x) (Monotone.f e1 (x , (0 , Monotone.f e0 x))))
         → Preorder-max-str.≤ (snd PΓ) (fst x) (fst y)
         → Preorder-max-str.≤ (snd PC)
             (natrec (Monotone.f e0 (fst x)) (λ n x₂ → Monotone.f e1 (fst x , n , x₂)) (snd x))
             (natrec (Monotone.f e0 (fst y)) (λ n x₂ → Monotone.f e1 (fst y , n , x₂)) (snd x))
  e0-lem {Γ , preorder-max ≤Γ reflΓ transΓ maxΓ max-lΓ max-rΓ max-lubΓ} {C , preorder-max ≤c reflc transc maxc max-lc max-rc max-lubc}
         (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , Z) (y , m) p q = e0-is-monotone x y q
  e0-lem {Γ , preorder-max ≤Γ reflΓ transΓ maxΓ max-lΓ max-rΓ max-lubΓ} {C , preorder-max ≤c reflc transc maxc max-lc max-rc max-lubc}
         (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , S n) (y , m) p q =
           e1-is-monotone (x , (n , natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) n))
                          (y , (n , natrec (e0 y) (λ n₁ x₂ → e1 (y , n₁ , x₂)) n))
                          (q ,
                            (Preorder-max-str.refl nat-p n , {!!})) --e0-lem (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) {!!} {!!} p q))

{- WTS:
      (e1 (x , n , natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) n))
   ≤c (e1 (y , n , natrec (e0 y) (λ n₁ x₂ → e1 (y , n₁ , x₂)) n))-}

  postulate
    hlem : ∀ {PΓ PC} → (e0 : MONOTONE PΓ PC) → (e1 : MONOTONE (PΓ ×p (PN ×p PC)) PC) → (x : fst (PΓ ×p PN))
       → (∀ x → Preorder-max-str.≤ (snd PC) (Monotone.f e0 x) (Monotone.f e1 (x , (0 , Monotone.f e0 x))))
       → Preorder-max-str.≤ (snd PC)
           (Monotone.f e0 (fst x))
           (Monotone.f e1 ((fst x) , (snd x) , natrec (Monotone.f e0 (fst x)) (λ n₁ x₂ → Monotone.f e1 ((fst x) , n₁ , x₂)) (snd x)))
{-  hlem {Γ , preorder-max ≤ refl trans max max-l max-r max-lub} {C , preorder-max ≤c reflc transc maxc max-lc max-rc max-lubc}
       (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , Z) p = p x
  hlem {Γ , preorder-max ≤ refl trans max max-l max-r max-lub} {C , preorder-max ≤c reflc transc maxc max-lc max-rc max-lubc}
       (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , S n) p =
         transc
           (e0 x)
           (e1 (x , (0 , (e0 x))))
           (e1 (x , S n , natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) (S n)))
             (p x)
             (e1-is-monotone {!!} {!!} {!!})-}

{-wts: ≤c (e1 (x , 0 , e0 x))
      (e1 (x , S n , natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) (S n)))-}

  e0-lem2 : ∀ {PΓ PC} → (e0 : MONOTONE PΓ PC) → (e1 : MONOTONE (PΓ ×p (PN ×p PC)) PC) → (x y : fst (PΓ ×p PN))
         → (∀ x → Preorder-max-str.≤ (snd PC) (Monotone.f e0 x) (Monotone.f e1 (x , (0 , Monotone.f e0 x))))
         → Preorder-max-str.≤ (snd PN) (snd x) (snd y)
         → Preorder-max-str.≤ (snd PC)
             (natrec (Monotone.f e0 (fst x)) (λ n x₂ → Monotone.f e1 (fst x , n , x₂)) (snd x))
             (natrec (Monotone.f e0 (fst x)) (λ n x₂ → Monotone.f e1 (fst x , n , x₂)) (snd y))
  e0-lem2 {Γ , preorder-max ≤ refl trans max max-l max-r max-lub} {C , preorder-max ≤c reflc transc maxc max-lc max-rc max-lubc}
          (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , Z) (y , Z) j p = reflc (e0 x)
  e0-lem2 {Γ , preorder-max ≤ refl trans max max-l max-r max-lub} {C , preorder-max ≤c reflc transc maxc max-lc max-rc max-lubc}
          (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , Z) (y , (S n)) j p =
            hlem (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , n) (λ x₁ → j x₁)
  e0-lem2 {Γ , preorder-max ≤ refl trans max max-l max-r max-lub} {C , preorder-max ≤c reflc transc maxc max-lc max-rc max-lubc}
          (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , (S m)) (y , Z) j ()
  e0-lem2 {Γ , preorder-max ≤ refl trans max max-l max-r max-lub} {C , preorder-max ≤c reflc transc maxc max-lc max-rc max-lubc}
          (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , (S m)) (y , (S n)) j p =
            {!!}

{-wts:  ≤c
      (e1 (x , m , natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) m))
      (e1 (x , n , natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) n))

have: ≤c
      (natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) m)
      (natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) n)-}

{-e0-lem2 (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , m) (y , n) j p-}

  rec' : ∀ {PΓ PC} → (e0 : MONOTONE PΓ PC) → (e1 : MONOTONE (PΓ ×p (PN ×p PC)) PC)
       → (∀ x → Preorder-max-str.≤ (snd PC) (Monotone.f e0 x) (Monotone.f e1 (x , (0 , Monotone.f e0 x))))
       → MONOTONE (PΓ ×p PN) PC
  rec' {Γ , preorder-max ≤Γ reflΓ transΓ maxΓ max-lΓ max-rΓ max-lubΓ} {C , preorder-max ≤c reflc transc maxc max-lc max-rc max-lubc}
       (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) p =
         monotone (λ x → natrec (e0 (fst x)) (λ n x₂ → e1 ((fst x) , (n , x₂))) (snd x))
           (λ x y x₁ →
             transc
               (natrec (e0 (fst x)) (λ n x₂ → e1 (fst x , n , x₂)) (snd x))
               (natrec (e0 (fst y)) (λ n x₂ → e1 (fst y , n , x₂)) (snd x))
               (natrec (e0 (fst y)) (λ n x₂ → e1 (fst y , n , x₂)) (snd y))
                 {!!}
                 {!!})

  pair' : ∀ {PΓ PA PB} → MONOTONE PΓ PA → MONOTONE PΓ PB → MONOTONE PΓ (PA ×p PB)
  pair' (monotone f f-ismono) (monotone g g-ismono) = monotone (λ x → (f x) , (g x)) (λ x y x₁ → (f-ismono x y x₁) , (g-ismono x y x₁))

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

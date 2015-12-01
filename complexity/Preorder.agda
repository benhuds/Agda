open import Preliminaries

module Preorder where

  record Preorder-str (A : Set) : Set1 where
    constructor preorder
    field
      ≤ : A → A → Set
      refl : ∀ x → ≤ x x
      trans : ∀ x y z → ≤ x y → ≤ y z → ≤ x z

------------------------------------------

  -- Task 1: Show that the Natural numbers with ≤ form a preorder

  -- the ≤ relation on Natural numbers
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
  nat-trans Z (S y) Z p q = abort q
  nat-trans Z (S y) (S z) p q = <>
  nat-trans (S x) Z Z () q
  nat-trans (S x) Z (S z) () q
  nat-trans (S x) (S y) Z p ()
  nat-trans (S x) (S y) (S z) p q = nat-trans x y z p q

  -- proof that Nat and ≤ (the ≤ relation defined on the natural numbers) form a preorder
  nat-p : Preorder-str Nat
  nat-p = record { ≤ = ≤nat; refl = nat-refl; trans = nat-trans }

------------------------------------------

  -- Task 2: Show that the product of two preorders is a preorder

  {- defining the relation: when is one cartesian product 'less than' another?
     if A and B are preorders and we have cartesian products (a1,b1) and (a2,b2)
     such that a1,a2 ∈ A and b1,b2 ∈ B,
     then (a1,b1)≤(a2,b2) iff a1≤a2 and b1≤b2
  -}
  ≤axb : ∀ {A B : Set} → Preorder-str A → Preorder-str B → (A × B) → (A × B) → Set
  ≤axb PA PB (a1 , b1) (a2 , b2) = Preorder-str.≤ PA a1 a2 × Preorder-str.≤ PB b1 b2

  {-  a cartesian product (a,b) is 'less than' itself
     if each component of the product is reflexive, i.e.
     just show that a is reflexive and b is reflexive
  -}
  axb-refl : ∀ {A B : Set} → (PA : Preorder-str A) → (PB : Preorder-str B) → (x : (A × B)) →  ≤axb PA PB x x
  axb-refl PA PB (a , b) = Preorder-str.refl PA a , Preorder-str.refl PB b

  -- same idea for transitivity...
  axb-trans : ∀ {A B : Set} → (PA : Preorder-str A) → (PB : Preorder-str B) → (x y z : (A × B)) → ≤axb PA PB x y → ≤axb PA PB y z → ≤axb PA PB x z
  axb-trans PA PB (a1 , b1) (a2 , b2) (a3 , b3) (a1<a2 , b1<b2) (a2<a3 , b2<b3) = 
                          Preorder-str.trans PA a1 a2 a3 a1<a2 a2<a3 , Preorder-str.trans PB b1 b2 b3 b1<b2 b2<b3

  -- proof that AxB is a preorder
  AxB-ispreorder : ∀ (A B : Set) → Preorder-str A → Preorder-str B → Preorder-str (A × B)
  AxB-ispreorder A B pre-a pre-b = record { ≤ = ≤axb pre-a pre-b; refl = axb-refl pre-a pre-b; trans = axb-trans pre-a pre-b } 

------------------------------------------

  -- Task 4: Show that given a Preorder A and Preorder B, Preorder (Monotone A B)

  -- the type of monotone functions from A to B
  -- i.e. functions which give you bigger outputs when you give them bigger inputs
  record Monotone (A : Set) (B : Set) (PA : Preorder-str A) (PB : Preorder-str B) : Set where
    constructor monotone
    field
      f : A → B
      is-monotone : ∀ (x y : A) → Preorder-str.≤ PA x y → Preorder-str.≤ PB (f x) (f y)

  -- the order on monotone functions is just the
  -- pointwise order on the underlying functions
  ≤mono : ∀ {A B : Set} → (PA : Preorder-str A) → (PB : Preorder-str B) → (Monotone A B PA PB) → (Monotone A B PA PB) → Set
  ≤mono {A} PA PB f g = (x : A) → Preorder-str.≤ PB (Monotone.f f x) (Monotone.f g x)

  mono-refl : ∀ {A B : Set} → (PA : Preorder-str A) → (PB : Preorder-str B) → (x : (Monotone A B PA PB)) → ≤mono PA PB x x
  mono-refl PA PB f = λ x → Preorder-str.refl PB (Monotone.f f x)

  mono-trans : ∀ {A B : Set} → (PA : Preorder-str A) → (PB : Preorder-str B) → (x y z : (Monotone A B PA PB)) → ≤mono PA PB x y → ≤mono PA PB y z → ≤mono PA PB x z
  mono-trans PA PB f g h p q = λ x → Preorder-str.trans PB (Monotone.f f x) (Monotone.f g x) (Monotone.f h x) (p x) (q x)

  monotone-ispreorder : ∀ (A B : Set) → (PA : Preorder-str A) → (PB : Preorder-str B) → Preorder-str (Monotone A B PA PB)
  monotone-ispreorder A B PA PB = preorder (≤mono PA PB) (mono-refl PA PB) (mono-trans PA PB)

------------------------------------------

-- New stuff: Interpreting types as preorders

  -- repackaging preorder as a type together with a Preorder structure on that type
  PREORDER = Σ (λ (A : Set) → Preorder-str A)

  MONOTONE : (PΓ PA : PREORDER) → Set
  MONOTONE (Γ , PΓ) (A , PA) = Monotone Γ A PΓ PA

  PN : PREORDER
  PN = Nat , nat-p
  
  -- some operations
  _×p_ : PREORDER → PREORDER → PREORDER
  (A , PA) ×p (B , PB) = A × B , AxB-ispreorder A B PA PB

  _->p_ : PREORDER → PREORDER → PREORDER
  (A , PA) ->p (B , PB) = Monotone A B PA PB , monotone-ispreorder A B PA PB

  -- Unit is a preorder
  unit-p : PREORDER
  unit-p = Unit , preorder (λ x y → Unit) (λ x → <>) (λ x y z _ _ → <>) 

  -- identity preserves monotonicity
  id : ∀ {Γ} → MONOTONE Γ Γ
  id = λ {Γ} → monotone (λ x → x) (λ x y x₁ → x₁)

  -- composition preserves monotonicity
  comp : ∀ {PA PB PC} → MONOTONE PA PB → MONOTONE PB PC → MONOTONE PA PC
  comp (monotone f f-ismono) (monotone g g-ismono) =
          monotone (λ x → g (f x)) (λ x y x₁ → g-ismono (f x) (f y) (f-ismono x y x₁))

  -- proofs that types like pairs etc. with preorders are monotone
  pair' : ∀ {PΓ PA PB} → MONOTONE PΓ PA → MONOTONE PΓ PB → MONOTONE PΓ (PA ×p PB)
  pair' (monotone f f-ismono) (monotone g g-ismono) =
          monotone (λ x → f x , g x) (λ x y z → f-ismono x y z , g-ismono x y z)

  fst' : ∀ {PΓ PA PB} → MONOTONE PΓ (PA ×p PB) → MONOTONE PΓ PA
  fst' (monotone f f-ismono) = 
          monotone (λ x → fst (f x)) (λ x y z → fst (f-ismono x y z))

  snd' : ∀ {PΓ PA PB} → MONOTONE PΓ (PA ×p PB) → MONOTONE PΓ PB
  snd' (monotone f f-ismono) = 
          monotone (λ x → snd (f x)) (λ x y z → snd (f-ismono x y z))

  lam' : ∀ {PΓ PA PB} → MONOTONE (PΓ ×p PA) PB → MONOTONE PΓ (PA ->p PB)
  lam' {Γ , preorder ≤Γ reflΓ transΓ} {a , preorder ≤a refla transa} {b , preorder ≤b reflb transb} (monotone f f-ismono) =
          monotone (λ x → monotone (λ p → f (x , p)) (λ a b c → f-ismono (x , a) (x , b) (reflΓ x , c))) (λ x y z w → f-ismono (x , w) (y , w) (z , refla w))

  app' : ∀ {PΓ PA PB} → MONOTONE PΓ (PA ->p PB) → MONOTONE PΓ PA → MONOTONE PΓ PB
  app' {Γ , preorder ≤Γ reflΓ transΓ} {a , preorder ≤a refla transa} {b , preorder ≤b reflb transb} (monotone f f-ismono) (monotone g g-ismono) =
          monotone (λ x → Monotone.f (f x) (g x)) (λ x y z → transb (Monotone.f (f x) (g x)) (Monotone.f (f y) (g x)) (Monotone.f (f y) (g y))
          (f-ismono x y z (g x)) (Monotone.is-monotone (f y) (g x) (g y) (g-ismono x y z)))

  z' : ∀ {PΓ} → MONOTONE PΓ PN
  z' = monotone (λ x → Z) (λ x y x₁ → <>)

  suc' : ∀ {PΓ} → MONOTONE PΓ PN → MONOTONE PΓ PN
  suc' {Γ , preorder ≤ refl trans} (monotone f f-is-monotone) = monotone (λ x → S (f x)) (λ x y x₁ → f-is-monotone x y x₁)

  natrec : ∀{C : Set} → (base : C) → (step : Nat → C → C) → (n : Nat) → C
  natrec base step Z = base
  natrec base step (S n) = step n (natrec base step n)

  h-lem : ∀ {PΓ PC} → (e0 : MONOTONE PΓ PC) → (e1 : MONOTONE (PΓ ×p (PN ×p PC)) PC) → (x y : fst (PΓ ×p PN))
         → (∀ x → Preorder-str.≤ (snd PC) (Monotone.f e0 x) (Monotone.f e1 (x , (0 , Monotone.f e0 x))))
         → Preorder-str.≤ (snd PΓ) (fst x) (fst y)
         → Preorder-str.≤ (snd PC)
             (natrec (Monotone.f e0 (fst x)) (λ n x₂ → Monotone.f e1 (fst x , n , x₂)) (snd x))
             (natrec (Monotone.f e0 (fst y)) (λ n x₂ → Monotone.f e1 (fst y , n , x₂)) (snd x))
  h-lem {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
         (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , Z) (y , m) p q = e0-is-monotone x y q
  h-lem {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
         (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , S n) (y , m) p q =
           e1-is-monotone
             (x , (n , natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) n))
             (y , (n , natrec (e0 y) (λ n₁ x₂ → e1 (y , n₁ , x₂)) n))
             (q , ((Preorder-str.refl nat-p n) ,
               h-lem {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
                 (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , n) (y , m) p q))

  h-lem2-lem : ∀ {PΓ PC} → (e0 : MONOTONE PΓ PC) → (e1 : MONOTONE (PΓ ×p (PN ×p PC)) PC) → (x : fst (PΓ ×p PN))
             → (∀ x → Preorder-str.≤ (snd PC) (Monotone.f e0 x) (Monotone.f e1 (x , (0 , Monotone.f e0 x))))
             → Preorder-str.≤ (snd PC)
               (Monotone.f e0 (fst x))
               (Monotone.f e1 ((fst x) , (snd x) , natrec (Monotone.f e0 (fst x)) (λ n₁ x₂ → Monotone.f e1 ((fst x) , n₁ , x₂)) (snd x)))
  h-lem2-lem {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
             (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , Z) p = p x
  h-lem2-lem {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
             (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , S n) p =
               transc
                 (e0 x)
                 (e1 (x , 0 , e0 x))
                 (e1 (x , S n , natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) (S n)))
                   (p x)
                   (e1-is-monotone (x , (0 , e0 x)) (x , S n , natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) (S n))
                     ((refl x) , (<> ,
                       h-lem2-lem {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
                         (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , n) p)))


  h-lem2 : ∀ {PΓ PC} → (e0 : MONOTONE PΓ PC) → (e1 : MONOTONE (PΓ ×p (PN ×p PC)) PC) → (x y : fst (PΓ ×p PN))
         → (∀ x → Preorder-str.≤ (snd PC) (Monotone.f e0 x) (Monotone.f e1 (x , (0 , Monotone.f e0 x))))
         → Preorder-str.≤ (snd PN) (snd x) (snd y)
         → Preorder-str.≤ (snd PC)
             (natrec (Monotone.f e0 (fst x)) (λ n x₂ → Monotone.f e1 (fst x , n , x₂)) (snd x))
             (natrec (Monotone.f e0 (fst x)) (λ n x₂ → Monotone.f e1 (fst x , n , x₂)) (snd y))
  h-lem2 {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
         (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , Z) (y , Z) p q = reflc (e0 x)
  h-lem2 {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
         (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , Z) (y , S n) p q =
           h-lem2-lem {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
             (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , n) (λ x₁ → p x₁)
  h-lem2 {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
         (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , S m) (y , Z) p ()
  h-lem2 {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
         (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , S m) (y , S n) p q =
           e1-is-monotone
             (x , m , natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) m)
             (x , n , natrec (e0 x) (λ n₁ x₂ → e1 (x , n₁ , x₂)) n)
             ((refl x) , (q ,
               h-lem2 {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
                 (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (x , m) (y , n) p q))

  rec' : ∀ {PΓ PC} → (e0 : MONOTONE PΓ PC) → (e1 : MONOTONE (PΓ ×p (PN ×p PC)) PC)
       → (∀ x → Preorder-str.≤ (snd PC) (Monotone.f e0 x) (Monotone.f e1 (x , (0 , Monotone.f e0 x))))
       → MONOTONE (PΓ ×p PN) PC
  rec' {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc} (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) p =
          monotone (λ x → natrec (e0 (fst x)) (λ n x₂ → e1 (fst x , n , x₂)) (snd x))
            (λ x y x₁ →
              transc
                (natrec (e0 (fst x)) (λ n x₂ → e1 (fst x , n , x₂)) (snd x))
                (natrec (e0 (fst y)) (λ n x₂ → e1 (fst y , n , x₂)) (snd x))
                (natrec (e0 (fst y)) (λ n x₂ → e1 (fst y , n , x₂)) (snd y))
                  (h-lem {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
                     (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone)
                     (fst x , snd x) (fst y , snd x) (λ x₂ → p x₂) (fst x₁))
                  (h-lem2 {Γ , preorder ≤ refl trans} {C , preorder ≤c reflc transc}
                     (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) (fst y , snd x) (fst y , snd y) (λ x₂ → p x₂) (snd x₁)))

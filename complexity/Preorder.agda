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

  --discrete nat
  nat-eq : Nat → Nat → Set
  nat-eq Z Z = Unit
  nat-eq Z (S n) = Void
  nat-eq (S m) Z = Void
  nat-eq (S m) (S n) = nat-eq m n

  ♭nat-refl : (x : Nat) → nat-eq x x
  ♭nat-refl Z = <>
  ♭nat-refl (S x) = ♭nat-refl x

  ♭nat-trans : (x y z : Nat) → nat-eq x y → nat-eq y z → nat-eq x z
  ♭nat-trans Z Z Z x x₁ = <>
  ♭nat-trans Z Z (S z) x ()
  ♭nat-trans Z (S y) z () x₁
  ♭nat-trans (S x) Z z () x₂
  ♭nat-trans (S x) (S y) Z x₁ x₂ = x₂
  ♭nat-trans (S x) (S y) (S z) x₁ x₂ = ♭nat-trans x y z x₁ x₂

  ♭nat-p : Preorder-str Nat
  ♭nat-p = preorder nat-eq ♭nat-refl ♭nat-trans

  --bools
  ≤b : Bool → Bool → Set
  ≤b True True = Unit
  ≤b True False = Void
  ≤b False True = Void
  ≤b False False = Unit

  b-refl : (x : Bool) → ≤b x x
  b-refl True = <>
  b-refl False = <>

  b-trans : (x y z : Bool) → ≤b x y → ≤b y z → ≤b x z
  b-trans True True True x x₁ = <>
  b-trans True True False x ()
  b-trans True False z () x₁
  b-trans False True z () x₁
  b-trans False False True x ()
  b-trans False False False x x₁ = <>

  bool-p : Preorder-str Bool
  bool-p = preorder ≤b b-refl b-trans

  --list
  ≤list : ∀ {A : Set} → List A → List A → Set
  ≤list [] [] = Unit
  ≤list [] (x :: l2) = Unit
  ≤list (x :: l1) [] = Void
  ≤list (x :: l1) (x₁ :: l2) = ≤list l1 l2

  l-refl : ∀ {A : Set} (l : List A) → ≤list l l
  l-refl [] = <>
  l-refl (x :: l) = l-refl l

  l-trans : ∀ {A : Set} (l1 l2 l3 : List A) → ≤list l1 l2 → ≤list l2 l3 → ≤list l1 l3
  l-trans [] [] [] x x₁ = <>
  l-trans [] [] (x :: l3) x₁ x₂ = <>
  l-trans [] (x :: l2) [] x₁ ()
  l-trans [] (x :: l2) (x₁ :: l3) x₂ x₃ = <>
  l-trans (x :: l1) [] l3 () x₂
  l-trans (x :: l1) (x₁ :: l2) [] x₂ ()
  l-trans (x :: l1) (x₁ :: l2) (x₂ :: l3) x₃ x₄ = l-trans l1 l2 l3 x₃ x₄

  list-p : ∀ {A : Set} → Preorder-str (List A)
  list-p = preorder ≤list l-refl l-trans

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
  axb-p : ∀ (A B : Set) → Preorder-str A → Preorder-str B → Preorder-str (A × B)
  axb-p A B pre-a pre-b = record { ≤ = ≤axb pre-a pre-b; refl = axb-refl pre-a pre-b; trans = axb-trans pre-a pre-b } 

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

  mono-p : ∀ (A B : Set) → (PA : Preorder-str A) → (PB : Preorder-str B) → Preorder-str (Monotone A B PA PB)
  mono-p A B PA PB = preorder (≤mono PA PB) (mono-refl PA PB) (mono-trans PA PB)

------------------------------------------

-- New stuff: Interpreting types as preorders

  -- repackaging preorder as a type together with a Preorder structure on that type
  PREORDER = Σ (λ (A : Set) → Preorder-str A)

  MONOTONE : (PΓ PA : PREORDER) → Set
  MONOTONE (Γ , PΓ) (A , PA) = Monotone Γ A PΓ PA

  PN : PREORDER
  PN = Nat , nat-p

  PL : (A : Set) → PREORDER
  PL A = (List A) , list-p
  
  -- some operations
  _×p_ : PREORDER → PREORDER → PREORDER
  (A , PA) ×p (B , PB) = A × B , axb-p A B PA PB

  _->p_ : PREORDER → PREORDER → PREORDER
  (A , PA) ->p (B , PB) = Monotone A B PA PB , mono-p A B PA PB

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

  --is this even correct
  lrec : ∀ {A C : Set} → (nil : C) → (cons : A → List A → List C → C) → (l : List A) → C
  lrec nil cons [] = nil
  lrec nil cons (x :: l) = cons x l (lrec nil cons l :: [])

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

{-
  plus' : ∀ {PΓ} → (e0 : MONOTONE PΓ PN) → (e1 : MONOTONE PΓ PN)
        → MONOTONE PΓ PN
  plus' {Γ , preorder ≤ refl trans} (monotone e0 e0-is-monotone) (monotone e1 e1-is-monotone) =
        monotone (λ x → e0 x + e1 x)
          (λ x y x₁ → Preorder-str.trans (snd PN)
                      (e0 x + e1 x)
                      (e0 y + e1 x)
                      (e0 y + e1 y)
                        {!!}
                        {!!})
-}
--- extend Preorders so you can impose max on them if type has maximums

  record Preorder-max-str {A : Set} (PA : Preorder-str A) : Set where
    constructor preorder-max
    field
      max : A → A → A
      max-l : ∀ l r → Preorder-str.≤ PA l (max l r)
      max-r : ∀ l r → Preorder-str.≤ PA r (max l r)
      max-lub : ∀ k l r → Preorder-str.≤ PA l k → Preorder-str.≤ PA r k → Preorder-str.≤ PA (max l r) k

  nat-max : Nat → Nat → Nat
  nat-max Z n = n
  nat-max (S m) Z = S m
  nat-max (S m) (S n) = S (nat-max m n)

  nat-max-l : ∀ (l r : Nat) → ≤nat l (nat-max l r)
  nat-max-l Z Z = <>
  nat-max-l Z (S n) = <>
  nat-max-l (S m) Z = nat-refl m
  nat-max-l (S m) (S n) = nat-max-l m n

  nat-max-r : ∀ (l r : Nat) → ≤nat r (nat-max l r)
  nat-max-r Z Z = <>
  nat-max-r Z (S n) = nat-refl n
  nat-max-r (S m) Z = <>
  nat-max-r (S m) (S n) = nat-max-r m n

  nat-max-lub : ∀ (k l r : Nat) → ≤nat l k → ≤nat r k → ≤nat (nat-max l r) k
  nat-max-lub Z Z Z p q = <>
  nat-max-lub Z Z (S r) p ()
  nat-max-lub Z (S l) Z () q
  nat-max-lub Z (S l) (S r) () q
  nat-max-lub (S k) Z Z p q = <>
  nat-max-lub (S k) Z (S r) p q = q
  nat-max-lub (S k) (S l) Z p q = p
  nat-max-lub (S k) (S l) (S r) p q = nat-max-lub k l r p q

  nat-pM : Preorder-max-str nat-p
  nat-pM = preorder-max nat-max nat-max-l nat-max-r nat-max-lub

  unit-pM : Preorder-max-str (snd unit-p)
  unit-pM = preorder-max (λ x x₁ → <>) (λ l r → <>) (λ l r → <>) (λ k l r x x₁ → <>)

  axb-max : ∀ {A B : Set} {PA : Preorder-str A} {PB : Preorder-str B}
          → Preorder-max-str PA → Preorder-max-str PB → (A × B) → (A × B) → (A × B)
  axb-max PA PB (a1 , b1) (a2 , b2) = Preorder-max-str.max PA a1 a2 , Preorder-max-str.max PB b1 b2

  axb-max-l : ∀ {A B : Set} {PA : Preorder-str A} {PB : Preorder-str B}
            → (PMA : Preorder-max-str PA) → (PMB : Preorder-max-str PB) → (l r : (A × B)) → ≤axb PA PB l (axb-max PMA PMB l r)
  axb-max-l PMA PMB (a1 , b1) (a2 , b2) = Preorder-max-str.max-l PMA a1 a2 , Preorder-max-str.max-l PMB b1 b2

  axb-max-r : ∀ {A B : Set} {PA : Preorder-str A} {PB : Preorder-str B}
            → (PMA : Preorder-max-str PA) → (PMB : Preorder-max-str PB) → (l r : (A × B)) → ≤axb PA PB r (axb-max PMA PMB l r)
  axb-max-r PMA PMB (a1 , b1) (a2 , b2) = Preorder-max-str.max-r PMA a1 a2 , Preorder-max-str.max-r PMB b1 b2

  axb-max-lub : ∀ {A B : Set} {PA : Preorder-str A} {PB : Preorder-str B} 
              → (PMA : Preorder-max-str PA) → (PMB : Preorder-max-str PB) → (k l r : (A × B)) 
              → ≤axb PA PB l k → ≤axb PA PB r k → ≤axb PA PB (axb-max PMA PMB l r) k
  axb-max-lub PMA PMB (k1 , k2) (l1 , l2) (r1 , r2) (l1<k1 , l2<k2) (r1<k1 , r2<k2) =
                 Preorder-max-str.max-lub PMA k1 l1 r1 l1<k1 r1<k1 , Preorder-max-str.max-lub PMB k2 l2 r2 l2<k2 r2<k2

  axb-pM : ∀ {A B : Set} {PA : Preorder-str A} {PB : Preorder-str B}
         → Preorder-max-str PA → Preorder-max-str PB → Preorder-max-str (axb-p A B PA PB)
  axb-pM PMA PMB = preorder-max (axb-max PMA PMB) (axb-max-l PMA PMB) (axb-max-r PMA PMB) (axb-max-lub PMA PMB)

  mono-max : ∀ {A B : Set} {PA : Preorder-str A} {PB : Preorder-str B}
           → Preorder-max-str PB
           → (Monotone A B PA PB) → (Monotone A B PA PB) → (Monotone A B PA PB)
  mono-max {A} {B} {PA} {PB} PMB (monotone f f-ismono) (monotone g g-ismono) =
           monotone (λ x → Preorder-max-str.max PMB (f x) (g x))
                    (λ x y x₁ → Preorder-max-str.max-lub PMB (Preorder-max-str.max PMB (f y) (g y)) (f x) (g x)
                    (Preorder-str.trans PB (f x) (f y)
                       (Preorder-max-str.max PMB (f y) (g y)) (f-ismono x y x₁)
                       (Preorder-max-str.max-l PMB (f y) (g y)))
                    (Preorder-str.trans PB (g x) (g y)
                       (Preorder-max-str.max PMB (f y) (g y)) (g-ismono x y x₁)
                       (Preorder-max-str.max-r PMB (f y) (g y))))

  mono-max-l : ∀ {A B : Set} {PA : Preorder-str A} {PB : Preorder-str B}
             → (PMB : Preorder-max-str PB) → (l r : Monotone A B PA PB) → ≤mono PA PB l (mono-max PMB l r)
  mono-max-l PMB f g = λ x → Preorder-max-str.max-l PMB (Monotone.f f x) (Monotone.f g x)

  mono-max-r : ∀ {A B : Set} {PA : Preorder-str A} {PB : Preorder-str B}
             → (PMB : Preorder-max-str PB) → (l r : Monotone A B PA PB) → ≤mono PA PB r (mono-max PMB l r)
  mono-max-r PMB f g = λ x → Preorder-max-str.max-r PMB (Monotone.f f x) (Monotone.f g x)

  mono-max-lub : ∀ {A B : Set} {PA : Preorder-str A} {PB : Preorder-str B}
               → (PMB : Preorder-max-str PB) 
               → (k l r : Monotone A B PA PB) 
               → ≤mono PA PB l k → ≤mono PA PB r k → ≤mono PA PB (mono-max PMB l r) k
  mono-max-lub PMB f g h p q = λ x → Preorder-max-str.max-lub PMB (Monotone.f f x) (Monotone.f g x) (Monotone.f h x) (p x) (q x)

  mono-pM : ∀ {A B : Set} {PA : Preorder-str A} {PB : Preorder-str B}
          → Preorder-max-str PB → Preorder-max-str (mono-p A B PA PB)
  mono-pM PMB = preorder-max (mono-max PMB) (mono-max-l PMB) (mono-max-r PMB) (mono-max-lub PMB)

  --???
  PREORDER-MAX = (Σ (λ (A : Set) → (PA : Preorder-str A) → Preorder-max-str PA))

{- Name: Bowornmet (Ben) Hudson

--Preorders in Agda!--

-}

open import Preliminaries

module Preorder where

  {- definition: a Preorder on a set A is a binary relation
     that is reflexive and transitive.
  -}
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
  nat-ispreorder : Preorder-str Nat
  nat-ispreorder = record { ≤ = ≤nat; refl = nat-refl; trans = nat-trans }

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

  -- Task 3: Show that the sum of two preorders is a preorder

  ≤a+b : ∀ {A B : Set} → Preorder-str A → Preorder-str B → (Either A B) → (Either A B) → Set
  ≤a+b (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inl a1) (Inl a2) = (a1 ≤a a2)
  ≤a+b (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inl a1) (Inr b2) = Void
  ≤a+b (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inr b1) (Inl a2) = Void
  ≤a+b (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inr b1) (Inr b2) = (b1 ≤b b2)

  a+b-refl : ∀ {A B : Set} → (a : Preorder-str A) → (b : Preorder-str B) → (x : (Either A B)) → ≤a+b a b x x
  a+b-refl (preorder _≤a_ refla transa) pre-b (Inl a) = refla a
  a+b-refl pre-a (preorder _≤b_ reflb transb) (Inr b) = reflb b

  a+b-trans : ∀ {A B : Set} → (a : Preorder-str A) → (b : Preorder-str B) → (x y z : (Either A B)) → ≤a+b a b x y → ≤a+b a b y z → ≤a+b a b x z
  a+b-trans (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inl a1) (Inl a2) (Inl a3) a1<a2 a2<a3 = transa a1 a2 a3 a1<a2 a2<a3
  a+b-trans (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inl a1) (Inl a2) (Inr b3) p ()
  a+b-trans (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inl a1) (Inr b2) (Inl a3) () q
  a+b-trans (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inl a1) (Inr b2) (Inr b3) () q
  a+b-trans (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inr b1) (Inl a2) (Inl a3) () q
  a+b-trans (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inr b1) (Inl a2) (Inr b3) () q
  a+b-trans (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inr b1) (Inr b2) (Inl a3) p ()
  a+b-trans (preorder _≤a_ refla transa) (preorder _≤b_ reflb transb) (Inr b1) (Inr b2) (Inr b3) b1<b2 b2<b3 = transb b1 b2 b3 b1<b2 b2<b3

  -- proof that A+B is a preorder
  A+B-ispreorder : ∀ (A B : Set) → Preorder-str A → Preorder-str B → Preorder-str (Either A B)
  A+B-ispreorder A B pre-a pre-b = record { ≤ = ≤a+b pre-a pre-b; refl = a+b-refl pre-a pre-b; trans = a+b-trans pre-a pre-b } 

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
  
  -- some operations
  _×p_ : PREORDER → PREORDER → PREORDER
  (A , PA) ×p (B , PB) = A × B , AxB-ispreorder A B PA PB

  _+p_ : PREORDER → PREORDER → PREORDER
  (A , PA) +p (B , PB) = Either A B , A+B-ispreorder A B PA PB

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

  inl' : ∀ {PΓ PA PB} → MONOTONE PΓ PA → MONOTONE PΓ (PA +p PB)
  inl' (monotone f f-ismono) =
          monotone (λ x → Inl (f x)) (λ x y z → f-ismono x y z)

  inr' : ∀ {PΓ PA PB} → MONOTONE PΓ PB → MONOTONE PΓ (PA +p PB)
  inr' (monotone f f-ismono) =
          monotone (λ x → Inr (f x)) (λ x y z → f-ismono x y z)

  case : ∀ {A B C : Set} → (A → C) → (B → C) → (Either A B → C)
  case a b (Inl x) = a x
  case a b (Inr x) = b x

  el : PREORDER → Set
  el = fst

  PREORDER≤ : (PA : PREORDER) → el PA → el PA → Set
  PREORDER≤ PA = Preorder-str.≤ (snd PA)

  -- oh my god
  lemma : ∀ {PA PB PC} {c1 c2 : el (PA +p PB)} {f1 f2 : el (PA ->p PC)} {g1 g2 : el (PB ->p PC)}
        → (PREORDER≤ (PA +p PB) c1 c2)
        → (PREORDER≤ (PA ->p PC) f1 f2) 
        → (PREORDER≤ (PB ->p PC) g1 g2) 
        → (PREORDER≤ PC (case (Monotone.f f1) (Monotone.f g1) c1) (case (Monotone.f f2) (Monotone.f g2) c2))
  lemma {A , preorder ≤a refla transa} {B , preorder ≤b reflb transb} {C , preorder ≤c reflc transc}
        {Inl a1} {Inl a2}
        {monotone f1 f1-ismono} {monotone f2 f2-ismono}
        a b c = transc (f1 a1) (f1 a2) (f2 a2) (f1-ismono a1 a2 a) (b a2)
  lemma {PA} {PB} {PC} {Inl a1} {Inr b1} () b c
  lemma {PA} {PB} {PC} {Inr b1} {Inl a1} () b c
  lemma {A , preorder ≤a refla transa} {B , preorder ≤b reflb transb} {C , preorder ≤c reflc transc}
        {Inr b1} {Inr b2}
        {monotone f1 f1-ismono} {monotone f2 f2-ismono} {monotone g1 g1-ismono} {monotone g2 g2-ismono}
        a b c = transc (g1 b1) (g1 b2) (g2 b2) (g1-ismono b1 b2 a) (c b2)

  lemma2 : ∀ {PΓ PA PC} → MONOTONE (PΓ ×p PA) PC → el PΓ → MONOTONE PA PC
  lemma2 {Γ , preorder ≤Γ reflΓ transΓ} (monotone f f-ismono) q = monotone (λ a → f (q , a)) (λ x y z → f-ismono (q , x) (q , y) (reflΓ q , z))

  case' : ∀ {PΓ PA PB PC} → MONOTONE (PΓ ×p PA) PC -> MONOTONE (PΓ ×p PB) PC -> MONOTONE PΓ (PA +p PB) -> MONOTONE PΓ PC
  case' {Γ , preorder ≤Γ reflΓ transΓ} {a , preorder ≤a refla transa} {b , preorder ≤b reflb transb} {c , preorder ≤c reflc transc}
        (monotone f f-ismono) (monotone g g-ismono) (monotone h h-ismono) =
          monotone (λ x → case (λ a → f (x , a)) (λ b → g (x , b)) (h x))
            (λ x y z → lemma {a , preorder ≤a refla transa} {b , preorder ≤b reflb transb} {c , preorder ≤c reflc transc} {h x} {h y}
            {lemma2 {Γ , preorder ≤Γ reflΓ transΓ}
               {a , preorder ≤a refla transa} {c , preorder ≤c reflc transc}
               (monotone f f-ismono) x}
            {lemma2 {Γ , preorder ≤Γ reflΓ transΓ}
               {a , preorder ≤a refla transa} {c , preorder ≤c reflc transc}
               (monotone f f-ismono) y}
            {lemma2 {Γ , preorder ≤Γ reflΓ transΓ}
               {b , preorder ≤b reflb transb} {c , preorder ≤c reflc transc}
               (monotone g g-ismono) x}
            {lemma2 {Γ , preorder ≤Γ reflΓ transΓ}
               {b , preorder ≤b reflb transb} {c , preorder ≤c reflc transc}
               (monotone g g-ismono) y}
                         (h-ismono x y z) (λ a₁ → f-ismono (x , a₁) (y , a₁) (z , refla a₁)) (λ b₁ → g-ismono (x , b₁) (y , b₁) (z , reflb b₁)))

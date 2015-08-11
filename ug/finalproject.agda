{- Name: Bowornmet (Ben) Hudson and Theodore (Ted) Kim

    -- COMP360 Final Project: Group Theory in Agda --

In this project, we define some fundamental ideas of group theory and
prove a few basic theorems about the topic using Agda. For example, we
define what a group is, and give several elementary examples of groups.
We utilize the notion of propositional equality in Agda to prove our
theorems using equation chains.

-}

open import Preliminaries

module finalproject where

  -- addition of nats
  plusNat : Nat → Nat → Nat
  plusNat Z m = m
  plusNat (S n) m = S (plusNat n m)

  -- integers
  data Int : Set where
    _-_ : (n : Nat) → (m : Nat) → Int

  -- negation
  -_ : Int → Int
  - (n - m) = m - n
 
  -- addition of ints
  plusInt : Int → Int → Int
  plusInt (n1 - m1) (n2 - m2) = plusNat n1 n2 - plusNat m1 m2

  -- operation
  Op : Set → Set
  Op el = el → el → el

  -- record of Group
  {- Definition: a Group is a set G with a binary operation, *, with three properties:
     1.) G has an identity element, e ∈ G, such that ∀ x ∈ G, e*x = x = x*e.
     2.) ∀ x ∈ G, ∃ x' ∈ G such that x*x' = e = x'*x, where e is the identity element of G.
     3.) G is associative. That is, ∀ x y z ∈ G, (x*y)*z = x*(y*z).
  -}
  record Group : Set1 where
    field
      el : Set
      _*_ : Op el
      e : el
      inv : el → el
      assoc :  ∀ x y z → ((x * y) * z) == (x * (y * z))
      ident-l : ∀ x → (e * x) == x
      ident-r : ∀ x → (x * e) == x
      inv-l : ∀ x → ((inv x) * x) == e
      inv-r : ∀ x → (x * (inv x)) == e

  -- first example, Bools with "multiplication" operation. Comparable to Z mod 2
  -- with addition

  -- multiplication of bools
  multB : Bool → Bool → Bool
  multB True True = True
  multB True False = False
  multB False True = False
  multB False False = True

  -- associativity of bools
  assocB : ∀ (x y z : Bool) → multB (multB x y) z == multB x (multB y z)
  assocB True True True = Refl
  assocB True True False = Refl
  assocB True False True = Refl
  assocB True False False = Refl
  assocB False True True = Refl
  assocB False True False = Refl
  assocB False False True = Refl
  assocB False False False = Refl

  -- proof of identity
  multTruel : ∀ (x : Bool) → (multB True x == x)
  multTruel True = Refl
  multTruel False = Refl

  multTruer : ∀ (x : Bool) → (multB x True == x)
  multTruer True = Refl
  multTruer False = Refl

  -- inverses of bools
  invB : Bool → Bool
  invB True = True
  invB False = False

  -- proof of inverses with identity
  invBMultl : ∀ (x : Bool) → (multB (invB x) x == True)
  invBMultl True = Refl
  invBMultl False = Refl

  invBMultr : ∀ (x : Bool) → (multB x (invB x) == True)
  invBMultr True = Refl
  invBMultr False = Refl

  -- proof that the Booleans are a group on multiplication
  Bool*-isgroup : Group
  Bool*-isgroup = record {
               el = Bool;
               _*_ = multB;
               e = True;
               inv = invB;
               assoc = assocB;
               ident-l = multTruel;
               ident-r = multTruer;
               inv-l = invBMultl;
               inv-r = invBMultr }

  -- second example of a group, ints with the addition operation

  -- congruence
  congruenceNatInt : ∀ (a b c d : Nat) → a == c → b == d → a - b == c - d
  congruenceNatInt .c .d c d Refl Refl = Refl 

  congruenceNat : ∀ (x y : Nat) → x == y → (S x) == (S y)
  congruenceNat .y y Refl = Refl

  congruenceNat' : ∀ (n m : Nat) → n == m → S n == S m
  congruenceNat' .m m Refl = Refl

  -- lemma
  addZNat : ∀ (x : Nat) → plusNat x Z == x
  addZNat Z = Refl
  addZNat (S x) = congruenceNat (plusNat x Z) x (addZNat x)

  -- proof of associativity
  assocNat+ : (x y z : Nat) → plusNat (plusNat x y) z == plusNat x (plusNat y z)
  assocNat+ Z y z = Refl
  assocNat+ (S x) y z = congruenceNat (plusNat (plusNat x y) z) (plusNat x (plusNat y z)) (assocNat+ x y z)

  assocInt+ : ∀ (a b c : Int) → plusInt (plusInt a b) c == plusInt a (plusInt b c)
  assocInt+ (n1 - m1) (n2 - m2) (n3 - m3) = congruenceNatInt (plusNat (plusNat n1 n2) n3)
                                              (plusNat (plusNat m1 m2) m3) (plusNat n1 (plusNat n2 n3))
                                              (plusNat m1 (plusNat m2 m3)) (assocNat+ n1 n2 n3) (assocNat+ m1 m2 m3) 

  -- proof of identity
  addIntZl : ∀ (n : Int) → (plusInt (Z - Z) n == n)
  addIntZl (n - m) = Refl

  addIntZr : ∀ (n : Int) → (plusInt n (Z - Z) == n)
  addIntZr (n - m) = congruenceNatInt (plusNat n 0) (plusNat m 0) n m (addZNat n) (addZNat m)

  -- proof of inverses
  -- issue with quotient type: impossible to prove that (S n) - (S n) = 0 - 0 without equality constructor
  -- had problems in including the equality constructor, only thing we could not work out
  invIntl : ∀ (n : Int) → plusInt (- n) n == (Z - Z)
  invIntl (n - m) = {!!}

  invIntr : ∀ (n : Int) → plusInt n (- n) == (Z - Z)
  invIntr (n - m) = {!!}

  -- proof that the integers on addition are a group
  Int+-isgroup : Group
  Int+-isgroup = record {
              el = Int;
              _*_ = plusInt;
              e = Z - Z;
              inv = -_;
              assoc = assocInt+;
              ident-l = addIntZl;
              ident-r = addIntZr;
              inv-l = invIntl;
              inv-r = invIntr }

   {- Definition: an group is called abelian if it is commutative.
      That is, ∀ x y ∈ G, x*y = y*x. Our record of an abelian group
      requires a group and a proof that the group operation
      is commutative.
   -}
  record AbelianGroup (G : Group) : Set where
    open Group G
    field
      comm : ∀ (x y : el) → x * y == y * x

  -- proof of commutativity for multiplication on bools
  commB : ∀ (x y : Bool) → multB x y == multB y x
  commB True True = Refl
  commB True False = Refl
  commB False True = Refl
  commB False False = Refl

  Bool*-isAbelian : AbelianGroup Bool*-isgroup
  Bool*-isAbelian = record {
                 comm = commB }

  -- some theorems
  module Theorems (G : Group) where
    open Group G
    congruenceOP : {a b c : el} → a == b → a * c == b * c
    congruenceOP Refl = Refl

    congruenceOP' : {a b c : el} → b == c → a * b == a * c
    congruenceOP' Refl = Refl

    sym : {a b : el} → a == b → b == a
    sym Refl = Refl

    -- extremely simple theorem
    babytheorem : (a b : el) → ((a * e) * b) == (a * b)
    babytheorem a b = congruenceOP (ident-r a)

    -- theorem 1: Let G be a group, and let a and b ∈ G. Then (a * b)^-1 = b^-1 * a^-1.
    theorem1 : ∀ (a b : el) → inv (a * b) == (inv b * inv a)
    theorem1 a b  = inv (a * b)                                      =⟨ sym (ident-r (inv (a * b))) ⟩
                    (inv (a * b) * e)                               =⟨ sym (congruenceOP' (inv-r a)) ⟩ 
                    (inv (a * b) * (a * inv a))                     =⟨ congruenceOP' (congruenceOP (sym (ident-r a))) ⟩
                    (inv (a * b) * ((a * e) * inv a))               =⟨ congruenceOP' (congruenceOP (congruenceOP' (sym (inv-r b)))) ⟩
                    (inv (a * b) * ((a * (b * inv b)) * inv a))     =⟨ congruenceOP' (congruenceOP (sym (assoc a b (inv b)))) ⟩
                    (inv (a * b) * (((a * b) * inv b) * inv a))     =⟨ congruenceOP' (assoc (a * b) (inv b) (inv a)) ⟩
                    (inv (a * b) * ((a * b) * (inv b * inv a)))     =⟨ sym (assoc (inv (a * b)) (a * b) (inv b * inv a)) ⟩
                    ((inv (a * b) * (a * b)) * (inv b * inv a))     =⟨ congruenceOP (inv-l (a * b)) ⟩
                    (e * (inv b * inv a))                           =⟨ ident-l (inv b * inv a) ⟩
                    (inv b * inv a)                                 ∎

    -- theorem 2: Let G be a group, and let a, b, and c ∈ G. If a * c = b * c, then a = b.
    theorem2 : ∀ (a b c : el) → (a * c) == (b * c) → a == b
    theorem2 a b c p = a                            =⟨ sym (ident-r a) ⟩
                       a * e                        =⟨ congruenceOP' (sym (inv-r c)) ⟩
                       (a * (c * inv c))            =⟨ sym (assoc a c (inv c)) ⟩
                       (a * c) * inv c              =⟨ congruenceOP p ⟩
                       (b * c) * inv c              =⟨ assoc b c (inv c) ⟩
                       (b * (c * inv c))            =⟨ congruenceOP' (inv-r c) ⟩
                       (b * e)                      =⟨ ident-r b ⟩
                       b                            ∎

    -- theorem 3: Let G be a group, and let g ∈ G. If g * g = g, then g = e.
    theorem3 : ∀ (g : el) → (g * g) == g → g == e
    theorem3 g p = g                       =⟨ sym (ident-r g) ⟩
                   (g * e)                 =⟨ congruenceOP' (sym (inv-r g)) ⟩
                   (g * (g * inv g))       =⟨ sym (assoc g g (inv g)) ⟩
                   (g * g) * inv g         =⟨ congruenceOP p ⟩
                   g * inv g               =⟨ inv-r g ⟩
                   e                       ∎

    -- lemma 1: for all x ∈ G, if x * x = e, x^-1 = x. That is, x is its own inverse.
    lemma1 : ∀ (x : el) → (p : x * x == e) → inv x == x
    lemma1 x p = (inv x)                          =⟨ sym (ident-r (inv x)) ⟩
                 (inv x * e)                      =⟨ congruenceOP' (sym p) ⟩
                 inv x * (x * x)                  =⟨ sym (assoc (inv x) x x) ⟩
                 (inv x * x) * x                  =⟨ congruenceOP (inv-l x) ⟩
                 (e * x)                          =⟨ ident-l x ⟩
                 x                                ∎                            

    -- theorem 4: let G be a group. If ∀ x ∈ G, x * x = e, then G is abelian.
    theorem4 : (p : ∀ x → (x * x) == e) → AbelianGroup G
    theorem4 p = record {
                comm = λ a b → a * b                            =⟨ congruenceOP (sym (ident-r a)) ⟩
                               (a * e) * b                      =⟨ congruenceOP (congruenceOP' (sym (inv-r a))) ⟩
                               (a * (a * inv a)) * b            =⟨ congruenceOP (sym (assoc a a (inv a))) ⟩
                               ((a * a) * inv a) * b            =⟨ congruenceOP (congruenceOP (p a)) ⟩
                               (e * inv a) * b                  =⟨ congruenceOP (ident-l (inv a)) ⟩
                               inv a * b                        =⟨ congruenceOP' (sym (ident-r b)) ⟩
                               inv a * (b * e)                  =⟨ congruenceOP' (congruenceOP' (sym (inv-r b))) ⟩
                               inv a * (b * (b * inv b))        =⟨ congruenceOP' (sym (assoc b b (inv b))) ⟩ 
                               inv a * ((b * b) * inv b)        =⟨ congruenceOP' (congruenceOP (p b)) ⟩
                               inv a * (e * inv b)              =⟨ congruenceOP' (ident-l (inv b)) ⟩
                               (inv a * inv b)                  =⟨ sym (theorem1 b a) ⟩
                               (inv (b * a))                    =⟨ lemma1 (b * a) (p (b * a)) ⟩
                               (b * a)                          ∎ }

    -- theorem 5: Let G be a group, and a, b, and c ∈ G. If (a * b) * c = e, then (b * c) * a = e as well.
    theorem5 : ∀ (a b c : el) → ((a * b) * c) == e → ((b * c) * a) == e 
    theorem5 a b c p = ((b * c) * a)                         =⟨ sym (ident-l ((b * c) * a)) ⟩
                       e * ((b * c) * a)                     =⟨ congruenceOP (sym (inv-l a)) ⟩
                       (inv a * a) * ((b * c) * a)           =⟨ assoc (inv a) a ((b * c) * a) ⟩
                       inv a * (a * ((b * c) * a))           =⟨ sym (congruenceOP' (assoc a (b * c) a)) ⟩
                       inv a * ((a * (b * c)) * a)           =⟨ congruenceOP' (congruenceOP (sym (assoc a b c))) ⟩
                       inv a * (((a * b) * c) * a)           =⟨ congruenceOP' (congruenceOP p) ⟩
                       inv a * (e * a)                       =⟨ congruenceOP' (ident-l a) ⟩
                       (inv a * a)                           =⟨ inv-l a ⟩
                       e                                     ∎

  {- Definition: a homomorphism is a function f from a group (G , *) to another group (H , ∘)
     such that (∀ a,b ∈ G), f(a*b) = f(a)∘f(b). Our definition of a homomorphism also includes a
     proof that homomorphisms preserve identity elements between groups. That is, f(e_G) = e_H,
     where e_G and e_H are the identity elements in G and H, respectively.
  -}
  -- record of homomorphisms
  record Homomorphism (G : Group) (H : Group) : Set where
    open Group renaming (_*_ to *)
    field
      f : el G → el H
      preserve-id : f (e G) == e H
      preserve-op : ∀ (a b : el G) → (f (* G a b)) == * H (f a) (f b)

  -- third example of a group, Z mod 2 under addition.
  -- Z mod 2
  data Zmod2 : Set where
    Zero : Zmod2
    One : Zmod2

  -- addition mod 2
  plusmod2 : Zmod2 → Zmod2 → Zmod2
  plusmod2 Zero Zero = Zero
  plusmod2 Zero One = One
  plusmod2 One Zero = One
  plusmod2 One One = Zero

  -- identity of Z mod 2
  idenZmod2-l : (x : Zmod2) → plusmod2 Zero x == x
  idenZmod2-l Zero = Refl
  idenZmod2-l One = Refl

  idenZmod2-r : (x : Zmod2) → plusmod2 x Zero == x
  idenZmod2-r Zero = Refl
  idenZmod2-r One = Refl

  -- inverses of Z mod 2 (the inverse of anything in Z mod 2 is itself)
  invZmod2 : Zmod2 → Zmod2
  invZmod2 x = x

  -- left and right inverses of Z mod 2
  invZmod2-lr : (x : Zmod2) → plusmod2 x x == Zero
  invZmod2-lr Zero = Refl
  invZmod2-lr One = Refl

  -- associativity of addition in Z mod 2
  assocZmod2 : (x y z : Zmod2) → plusmod2 (plusmod2 x y) z == plusmod2 x (plusmod2 y z)
  assocZmod2 Zero Zero Zero = Refl
  assocZmod2 Zero Zero One = Refl
  assocZmod2 Zero One Zero = Refl
  assocZmod2 Zero One One = Refl
  assocZmod2 One Zero Zero = Refl
  assocZmod2 One Zero One = Refl
  assocZmod2 One One Zero = Refl
  assocZmod2 One One One = Refl

  -- commutativity of addition in Z mod 2
  commZmod2 : (x y : Zmod2) → plusmod2 x y == plusmod2 y x
  commZmod2 Zero Zero = Refl
  commZmod2 Zero One = Refl
  commZmod2 One Zero = Refl
  commZmod2 One One = Refl

  -- Zmod2 is a group on addition.
  Zmod2+-isgroup : Group
  Zmod2+-isgroup = record {
                el = Zmod2;
                _*_ = plusmod2;
                e = Zero;
                inv = invZmod2;
                assoc = assocZmod2;
                ident-l = idenZmod2-l;
                ident-r = idenZmod2-r;
                inv-l = λ x → invZmod2-lr x;
                inv-r = λ x → invZmod2-lr x }

  -- proof that Z mod 2 on addition is an abelian group.
  Zmod2+-isAbelian : AbelianGroup (Zmod2+-isgroup)
  Zmod2+-isAbelian = record {
                  comm = commZmod2 }

  -- example of a homomorphism: mapBool-to-Zmod2 is a homomorphism from Bools on multiplication to Zmod2 with addition.
  -- map from Bools to the elements of Zmod2.
  mapBool-to-Zmod2 : Bool → Zmod2
  mapBool-to-Zmod2 True = Zero
  mapBool-to-Zmod2 False = One

  -- proof that the map from Bools to Zmod2 preserves composition.
  mapBool-to-Zmod2-preserve-op : (a b : Bool) → mapBool-to-Zmod2 (multB a b) == plusmod2 (mapBool-to-Zmod2 a) (mapBool-to-Zmod2 b)
  mapBool-to-Zmod2-preserve-op True True = Refl
  mapBool-to-Zmod2-preserve-op True False = Refl
  mapBool-to-Zmod2-preserve-op False True = Refl
  mapBool-to-Zmod2-preserve-op False False = Refl

  homomorphism-example : Homomorphism (Bool*-isgroup) (Zmod2+-isgroup)
  homomorphism-example = record {
                      f = mapBool-to-Zmod2;
                      preserve-id = Refl;
                      preserve-op = mapBool-to-Zmod2-preserve-op }

   -- record of isomorphisms.
  {- Definition: a homomorphism between two groups is called an isomorphism
     if it is bijective (both one-to-one and onto). The isomorphism record
     requires a homomorphism along with proofs that it is both one-to-one
     (injective) and onto (surjective).
  -}
  record Isomorphism (G : Group) (H : Group) : Set where
    open Group
    open Homomorphism
    field
      homomorphism : Homomorphism G H
      injective : ∀ (a b : el G) → f homomorphism a == f homomorphism b → a == b
      surjective : ∀ (b : el H) → Σ (λ g → f homomorphism g == b)

  -- example of an isomorphism
  -- proof that this map from Bools to Zmod2 is injective (that is, ∀ a b : Bool, f(a) = f(b) implies a = b).
  mapB-Zmod2-inj : (a b : Bool) → mapBool-to-Zmod2 a == mapBool-to-Zmod2 b → a == b 
  mapB-Zmod2-inj True True p = Refl
  mapB-Zmod2-inj True False ()
  mapB-Zmod2-inj False True ()
  mapB-Zmod2-inj False False p = Refl

  -- proof that this map from Bools to Zmod2 is surjective (that is, ∀ b : Zmod2, ∃ a ∈ Bool such that f(a) = b).
  mapB-Zmod2-sur : (n : Zmod2) → Σ (λ bool → mapBool-to-Zmod2 bool == n)
  mapB-Zmod2-sur Zero = True , Refl
  mapB-Zmod2-sur One = False , Refl

  -- the homomorphism between Bools on multiplication to Zmod2 with addition is isomorphic
  isomorphism-example : Isomorphism Bool*-isgroup Zmod2+-isgroup
  isomorphism-example = record { 
                     homomorphism = homomorphism-example;
                     injective = mapB-Zmod2-inj;
                     surjective = mapB-Zmod2-sur }


module Preliminaries where

  open import Agda.Primitive using (Level) renaming (lzero to lZ; lsuc to lS; _⊔_ to lmax)

  -- ----------------------------------------------------------------------
  -- functions

  _o_ : {A B C : Set} → (B → C) → (A → B) → A → C
  g o f = \ x → g (f x)
  infixr 10 _o_

  -- ----------------------------------------------------------------------
  -- identity type

  data _==_ {l : Level} {A : Set l} (M : A) : A → Set l where
    Refl : M == M

  Id : {l : Level} {A : Set l} (M : A) → A → Set l
  Id M N = M == N

  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL Refl #-}

  transport : {l1 : Level} {l2 : Level} {A : Set l1} (B : A → Set l2) 
              {a1 a2 : A} → a1 == a2 → (B a1 → B a2)
  transport B Refl = λ x → x

  ! : {l : Level} {A : Set l} {M N : A} → M == N → N == M 
  ! Refl = Refl

  _∘_  : {l : Level} {A : Set l} {M N P : A} 
      → N == P → M == N → M == P
  β ∘ Refl = β

  ap :  {l1 l2 : Level} {A : Set l1} {B : Set l2} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
  ap f Refl = Refl

  ap2 : {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3} {M N : A} {M' N' : B}
        (f : A -> B -> C) -> M == N -> M' == N' -> (f M M') == (f N N')
  ap2 f Refl Refl = Refl

  ap3 : {l1 l2 l3 l4 : Level} {A : Set l1} {B : Set l2} {C : Set l3} {D : Set l4} {M N : A} {M' N' : B} {M'' N'' : C}
      (f : A → B → C → D) → M == N → M' == N' → M'' == N'' → (f M M' M'') == (f N N' N'')
  ap3 f Refl Refl Refl = Refl

  ap4 : {l1 l2 l3 l4 l5 : Level} {A : Set l1} {B : Set l2} {C : Set l3} {D : Set l4} {E : Set l5} {M N : A} {M' N' : B} {M'' N'' : C} {M''' N''' : D}
      (f : A → B → C → D → E) → M == N → M' == N' → M'' == N'' → M''' == N''' → (f M M' M'' M''') == (f N N' N'' N''')
  ap4 f Refl Refl Refl Refl = Refl

  postulate
    -- function extensionality
    λ=  : {l1 l2 : Level} {A : Set l1} {B : A -> Set l2} {f g : (x : A) -> B x} -> ((x : A) -> (f x) == (g x)) -> f == g
    -- function extensionality for implicit functions
    λ=i  : {l1 l2 : Level} {A : Set l1} {B : A -> Set l2} {f g : {x : A} -> B x} -> ((x : A) -> (f {x}) == (g {x})) -> _==_ {_}{ {x : A} → B x } f g

  private primitive primTrustMe : {l : Level} {A : Set l} {x y : A} -> x == y

  infixr 9 _==_


  infix  2 _∎
  infixr 2 _=⟨_⟩_
  
  _=⟨_⟩_ : {l : Level} {A : Set l} (x : A) {y z : A} → x == y → y == z → x == z
  _ =⟨ p1 ⟩ p2 = (p2 ∘ p1)
  
  _∎ : {l : Level} {A : Set l} (x : A) → x == x
  _∎ _ = Refl


  -- ----------------------------------------------------------------------
  -- product types

  record Unit : Set where
    constructor <> 
  
  record Σ {l1 l2 : Level} {A : Set l1} (B : A -> Set l2) : Set (lmax l1 l2) where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σ public

  infixr 0 _,_

  _×_ : {l1 l2 : Level} → Set l1 -> Set l2 -> Set (lmax l1 l2)
  A × B = Σ (\ (_ : A) -> B)

  infixr 10 _×_

  -- ----------------------------------------------------------------------
  -- booleans

  data Bool : Set where
     True : Bool
     False : Bool
  {-# COMPILED_DATA Bool Bool True False #-}
  {-# BUILTIN BOOL  Bool  #-}
  {-# BUILTIN TRUE  True  #-}
  {-# BUILTIN FALSE False #-}

  -- ----------------------------------------------------------------------
  -- order

  data Order : Set where
    Less : Order
    Equal : Order
    Greater : Order

  -- ----------------------------------------------------------------------
  -- sums

  data Void : Set where

  abort : {A : Set} → Void → A
  abort () 

  data Either (A B : Set) : Set where
    Inl : A → Either A B
    Inr : B → Either A B

  DecEq : Set → Set
  DecEq A = (x y : A) → Either (x == y) (x == y → Void)

  -- ----------------------------------------------------------------------
  -- natural numbers

  module Nat where
    data Nat : Set where
      Z : Nat
      S : Nat -> Nat

    -- let's you use numerals for Nat
    {-# BUILTIN NATURAL Nat #-}

    _+_ : Nat → Nat → Nat
    Z + n = n
    (S m) + n = S (m + n)

    max : Nat → Nat → Nat
    max Z n = n
    max m Z = m
    max (S m) (S n) = S (max m n)

    equal : Nat → Nat → Bool
    equal Z Z = True
    equal Z (S _) = False
    equal (S _) Z = False
    equal (S m) (S n) = equal m n

    compare : Nat → Nat → Order
    compare Z Z = Equal
    compare Z (S m) = Less
    compare (S n) Z = Greater
    compare (S n) (S m) = compare n m

  open Nat public using (Nat ; Z ; S)


  -- ----------------------------------------------------------------------
  -- monad 

  module Monad where

    record Monad : Set1 where
      field 
        T : Set → Set
        return : ∀ {A} → A → T A
        _>>=_  : ∀ {A B} → T A → (A → T B) -> T B


  -- ----------------------------------------------------------------------
  -- options 
  
  module Maybe where

    data Maybe {l : Level} (A : Set l) : Set l where
      Some : A → Maybe A
      None : Maybe A

    Monad : Monad.Monad 
    Monad = record { T = Maybe; return = Some; _>>=_ = (λ {None _ → None; (Some v) f → f v}) }

  open Maybe public using (Maybe;Some;None)

  -- ----------------------------------------------------------------------
  -- lists

  module List where
    data List {l : Level} (A : Set l) : Set l where
      []  : List A
      _::_ : A -> List A -> List A
  
    {-# COMPILED_DATA List [] [] (:) #-}
    {-# BUILTIN LIST List #-}
    {-# BUILTIN NIL [] #-}
    {-# BUILTIN CONS _::_ #-}
  
    infixr 99 _::_
  
    _++_ : {A : Set} → List A → List A → List A
    [] ++ ys = ys
    (x :: xs) ++ ys = x :: (xs ++ ys)

    infixr 10 _++_

    map : {l1 l2 : Level} {A : Set l1} {B : Set l2} → (A → B) → List A → List B
    map f [] = []
    map f (x :: xs) = f x :: map f xs

    map-id : {l : Level} {A : Set l} (l : List A) → map (\ (x : A) → x) l == l
    map-id [] = Refl
    map-id (x :: l) with map (\ x -> x) l | map-id l
    ... | ._ | Refl = Refl
  
    ++-assoc : ∀ {A} (l1 l2 l3 : List A) → (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3)
    ++-assoc [] l2 l3 = Refl
    ++-assoc (x :: xs) l2 l3 = ap (_::_ x) (++-assoc xs l2 l3)

  open List public using (List ; [] ; _::_)


  -- ----------------------------------------------------------------------
  -- characters

  module Char where

    postulate {- Agda Primitive -}
      Char : Set
  
    {-# BUILTIN CHAR Char #-}
    {-# COMPILED_TYPE Char Char #-}
  
    private
     primitive
      primCharToNat    : Char → Nat
      primCharEquality : Char → Char → Bool
    
    toNat : Char → Nat
    toNat = primCharToNat
    
    equalb : Char -> Char -> Bool
    equalb = primCharEquality

    -- need to go outside the real language a little to give the primitives good types,
    -- but from the outside this should be safe
    equal : DecEq Char
    equal x y with equalb x y 
    ... | True = Inl primTrustMe
    ... | False = Inr canthappen where
      postulate canthappen : _

  open Char public using (Char)

  -- ----------------------------------------------------------------------
  -- vectors

  module Vector where

    data Vec (A : Set) : Nat → Set where
      []   : Vec A 0
      _::_ : ∀ {n} → A → Vec A n → Vec A (S n)

    infixr 99 _::_

    Vec-elim : {A : Set} (P : {n : Nat} → Vec A n → Set)
               → (P [])
               → ({n : Nat} (x : A) (xs : Vec A n) → P xs → P (x :: xs))
               → {n : Nat} (v : Vec A n) → P v
    Vec-elim P n c [] = n
    Vec-elim P n c (y :: ys) = c y ys (Vec-elim P n c ys)

    fromList : {A : Set} → List A → Σ \n → Vec A n
    fromList [] = _ , []
    fromList (x :: xs) = _ , x :: snd (fromList xs)

    toList : {A : Set} {n : Nat} → Vec A n → List A
    toList [] = []
    toList (x :: xs) = x :: (toList xs)

    toList' : {A : Set} → (Σ \ n → Vec A n) → List A
    toList' (._ , []) = []
    toList' (._ , (x :: xs)) = x :: (toList' (_ , xs))

  -- ----------------------------------------------------------------------
  -- strings

  module String where

    postulate {- Agda Primitive -}
      String : Set
    {-# BUILTIN STRING  String #-}
    {-# COMPILED_TYPE String String #-}

    private
      primitive
         primStringToList   : String -> List Char
         primStringFromList : List Char -> String
         primStringAppend   : String -> String -> String
         primStringEquality : String -> String -> Bool
  
    equal : String -> String -> Bool
    equal = primStringEquality
  
    toList = primStringToList
    fromList = primStringFromList
  
    append = primStringAppend

    toVec : String -> Σ \ m → Vector.Vec Char m
    toVec = Vector.fromList o toList
    


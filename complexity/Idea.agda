open import Preliminaries

module Idea where

  {- de Bruijn indices are representd as proofs that 
     an element is in a list -}
  data _∈_ {A : Set} : (x : A) (l : List A) → Set where -- type \in
    i0 : {x : A} {xs : List A} → x ∈ x :: xs
    iS : {x y : A} {xs : List A} → x ∈ xs → x ∈ y :: xs

  {- types of the STLC -}
  data Tp : Set where
    b : Tp             -- uninterpreted base type
    _⇒_ : Tp → Tp → Tp -- type \=>

  {- contexts are lists of Tp's -}
  Ctx = List Tp
  _,,_ : Ctx → Tp → Ctx
  Γ ,, τ = τ :: Γ

  infixr 10 _⇒_
  infixr 9 _,,_
  infixr 8 _⊢_ -- type \entails
  infix 9 _⊇_

  data _⊢_ (Γ : Ctx) : Tp → Set
  data _≡_ {Γ : Ctx} : {τ : Tp} → Γ ⊢ τ → Γ ⊢ τ → Set
  _⊢c_ : Ctx → Ctx → Set
  _⊇_ : Ctx → Ctx → Set -- type \sup=
  ids : {Γ : Ctx} → Γ ⊢c Γ
  rename : {Γ Γ' : Ctx} {τ : Tp} → Γ' ⊇ Γ → Γ ⊢ τ → Γ' ⊢ τ
  subst : {Γ Γ' : Ctx}{τ : Tp} → Γ ⊢c Γ' → Γ' ⊢ τ  → Γ ⊢ τ
  _·ss_ : {Γ1 Γ2 Γ3 : Ctx} → Γ1 ⊢c Γ2 → Γ2 ⊢c Γ3 → Γ1 ⊢c Γ3
  subst1 : {Γ : Ctx} {τ τ0 : Tp} → Γ ⊢ τ0 → (Γ ,, τ0) ⊢ τ → Γ ⊢ τ

  {- Γ ⊢ τ represents a term of type τ in context Γ -}
  data _⊢_ (Γ : Ctx) where
    c   : Γ ⊢ b -- some constant of the base type
    v   : {τ : Tp} 
        → τ ∈ Γ
        → Γ ⊢ τ 
    lam : {τ1 τ2 : Tp} 
        → Γ ,, τ1 ⊢ τ2
        → Γ ⊢ τ1 ⇒ τ2
    app : {τ1 τ2 : Tp} 
        → Γ ⊢ τ1 ⇒ τ2 
        → Γ ⊢ τ1 
        → Γ ⊢ τ2
    foo : {A : Tp} (e1 e2 : Γ ⊢ A) → e1 ≡ e2 → Γ ⊢ A

{-foo : (e1 : ™ Gamma A) (e2 : ™ Gamma A) -> e1 \equiv e2 -> ™ Gamma A-}

  Γ' ⊇ [] = Unit
  Γ' ⊇ (τ :: Γ) = (Γ' ⊇ Γ) × (τ ∈ Γ')

  rename-var : {Γ Γ' : Ctx} {τ : Tp} → Γ' ⊇ Γ → τ ∈ Γ → τ ∈ Γ'
  rename-var (ρ , x') i0 = x'
  rename-var (ρ , _) (iS x) = rename-var ρ x

  p· : {Γ : Ctx} {Γ' : Ctx} → Γ ⊇ Γ' → {τ : Tp} → (Γ ,, τ) ⊇ Γ'
  p· {Γ' = []} ren = <>
  p· {Γ' = (τ :: Γ')} (ρ , x) = p· ρ , iS x

  idr : {Γ : Ctx} → Γ ⊇ Γ
  idr {[]} = <>
  idr {τ :: Γ} = p· idr , i0

  -- category with families notation
  p : {Γ : Ctx} {τ : Tp} → (Γ ,, τ ⊇ Γ) 
  p = p· idr 

  addvar-ren : {Γ Γ' : Ctx} {τ : Tp} → Γ' ⊇ Γ → Γ' ,, τ ⊇ Γ ,, τ
  addvar-ren ρ = (p· ρ , i0)

  data _≡_ {Γ : Ctx} where
    CongApp  : {τ1 τ2 : Tp} {e e' : Γ ⊢ τ1 ⇒ τ2} {e1 e1' : Γ ⊢ τ1}
           → e ≡ e' → e1 ≡ e1'
           → (app e e1) ≡ (app e' e1')
    CongLam : {τ1 τ2 : Tp} {e e' : (τ1 :: Γ) ⊢ τ2} 
           → e ≡ e'
           → (lam e) ≡ (lam e')
    SubstId : ∀ {τ} {e : Γ ⊢ τ} → subst ids e ≡ e
    SubstComp : ∀ {Γ1 Γ2} {τ} {θ' : Γ ⊢c Γ2} {θ : Γ2 ⊢c Γ1} {e : Γ1 ⊢ τ} → subst θ' (subst θ e) ≡ subst (θ' ·ss θ) e
    Stepβ : {τ1 τ2 : Tp} {e : Γ ,, τ1 ⊢ τ2} {e1 : Γ ⊢ τ1}
           → (app (lam e) e1) ≡ subst1 e1 e 
    Refl : {τ : Tp} {e : Γ ⊢ τ} → e ≡ e
    Trans : {τ : Tp} {e1 e2 e3 : Γ ⊢ τ} 
         → e1 ≡ e2  →  e2 ≡ e3
         → e1 ≡ e3
    SubstCong : ∀ {Γ2} {τ} {Θ : Γ ⊢c Γ2} {e1 e2 : Γ2 ⊢ τ} → e1 ≡ e2 → subst Θ e1 ≡ subst Θ e2
    RenCong : ∀ {Γ2} {τ} {ρ : Γ ⊇ Γ2} {e1 e2 : Γ2 ⊢ τ} → e1 ≡ e2 → rename ρ e1 ≡ rename ρ e2

  rename ρ c = c
  rename ρ (v x) = v (rename-var ρ x)
  rename ρ (lam e) = lam (rename (addvar-ren ρ) e)
  rename ρ (app e e') = app (rename ρ e) (rename ρ e')
  rename ρ (foo e1 e2 p) = foo (rename ρ e1) (rename ρ e2) (RenCong p)

  _·rr_ : {Γ1 Γ2 Γ3 : Ctx} → Γ1 ⊇ Γ2 → Γ2 ⊇ Γ3 → Γ1 ⊇ Γ3
  _·rr_ {Γ1} {Γ2} {[]} ρ2 ρ3 = <>
  _·rr_ {Γ1} {Γ2} {x :: Γ3} ρ2 (ρ3 , x3) = (ρ2 ·rr ρ3) , rename-var ρ2 x3

  Γ' ⊢c [] = Unit
  Γ' ⊢c (τ :: Γ) = (Γ' ⊢c Γ) × (Γ' ⊢ τ) 
  
  _·rs_ : {Γ1 Γ2 Γ3 : Ctx} →  Γ1 ⊇ Γ2 → Γ2 ⊢c Γ3 → Γ1 ⊢c Γ3
  _·rs_ {Γ1} {Γ2} {[]} ρ θ = <>
  _·rs_ {Γ1} {Γ2} {τ3 :: Γ3} ρ (θ , e) = ρ ·rs θ , rename ρ e
  
  addvar : {Γ Γ' : Ctx} {τ : Tp} → Γ ⊢c Γ' → (Γ ,, τ) ⊢c (Γ' ,, τ)
  addvar θ = p ·rs θ , v i0
  
  ids {[]} = <>
  ids {τ :: Γ} = p ·rs ids , v i0
  
  subst-var : {Γ Γ' : Ctx}{τ : Tp} → Γ ⊢c Γ' → τ ∈ Γ' → Γ ⊢ τ
  subst-var (θ , e) i0 = e
  subst-var (θ , _) (iS x) = subst-var θ x
  
  subst1 e0 e = subst (ids , e0) e

  -- composition of renamings and substitutions

  _·sr_ : {Γ1 Γ2 Γ3 : Ctx} →  Γ1 ⊢c Γ2 → Γ2 ⊇ Γ3 → Γ1 ⊢c Γ3
  _·sr_ {Γ1} {Γ2} {[]} θ ρ = <>
  _·sr_ {Γ1} {Γ2} {τ3 :: Γ3} θ (ρ , x) = _·sr_ θ ρ , subst-var θ x

  _·ss_ {Γ3 = []} θ1 θ2 = <>
  _·ss_ {Γ1} {Γ2} {τ :: Γ3} θ1 (θ2 , e2) = θ1 ·ss θ2 , subst θ1 e2

  subst θ c = c
  subst θ (v x) = subst-var θ x
  subst θ (lam e) = lam (subst (addvar θ) e)
  subst θ (app e e') = app (subst θ e) (subst θ e')
  subst {Γ} {Γ'} {τ} Θ (foo e1 e2 p) = foo (subst Θ e1) (subst Θ e2) (SubstCong p)

  postulate
    semfoo : (A : Set) (x y : A) -> x == y -> A

  module Semantics (B : Set) (elB : B) where 

    ⟦_⟧t : Tp → Set
    ⟦_⟧c : Ctx → Set
    ⟦_⟧v : {Γ : Ctx} {τ : Tp} → τ ∈ Γ → ⟦ Γ ⟧c → ⟦ τ ⟧t
    ⟦_⟧ : {Γ : Ctx} {τ : Tp} → Γ ⊢ τ → ⟦ Γ ⟧c → ⟦ τ ⟧t
    sound : {Γ : Ctx} {τ : Tp} {e : Γ ⊢ τ} {e' : Γ ⊢ τ} → e ≡ e'
          → (γ : ⟦ Γ ⟧c) → ⟦ e ⟧ γ == ⟦ e' ⟧ γ

    ⟦ b ⟧t = B
    ⟦ τ1 ⇒ τ2 ⟧t = ⟦ τ1 ⟧t → ⟦ τ2 ⟧t

    ⟦ [] ⟧c = Unit
    ⟦ τ :: Γ ⟧c = ⟦ Γ ⟧c × ⟦ τ ⟧t

    ⟦_⟧v i0 γ = snd γ
    ⟦_⟧v (iS x) γ = ⟦ x ⟧v (fst γ)

    ⟦ c ⟧ γ = elB
    ⟦ v x ⟧ γ = ⟦ x ⟧v γ
    ⟦ lam e ⟧ γ = \ x → ⟦ e ⟧ (γ , x)
    ⟦ app e1 e2 ⟧ γ = ⟦ e1 ⟧ γ (⟦ e2 ⟧ γ)
    ⟦ (foo e1 e2 p) ⟧ γ = semfoo {!!} (⟦ e1 ⟧ γ) (⟦ e2 ⟧ γ) (sound {_} {_} {e1} {e2} p γ)

    ⟦_⟧s : {Γ Γ' : Ctx} → Γ ⊢c Γ' → ⟦ Γ ⟧c → ⟦ Γ' ⟧c
    ⟦_⟧s {Γ' = []} θ _ = <>
    ⟦_⟧s {Γ' = τ :: Γ'} (θ , e) γ = ⟦ θ ⟧s γ , ⟦ e ⟧ γ

    ⟦_⟧r : {Γ Γ' : Ctx} → Γ ⊇ Γ' → ⟦ Γ ⟧c → ⟦ Γ' ⟧c
    ⟦_⟧r {Γ' = []} θ _ = <>
    ⟦_⟧r {Γ' = τ :: Γ'} (θ , x) γ = ⟦ θ ⟧r γ , ⟦ x ⟧v γ

    interp-rename-var : {Γ' Γ : Ctx} {τ : Tp} (x : τ ∈ Γ) (θ : Γ' ⊇ Γ)
             → (γ' : ⟦ Γ' ⟧c) → ⟦ rename-var θ x ⟧v γ' == (⟦ x ⟧v (⟦ θ  ⟧r γ'))
    interp-rename-var i0 θ γ' = Refl
    interp-rename-var (iS x) θ γ' = interp-rename-var x (fst θ) γ'

    interp-subst-var : {Γ' Γ : Ctx} {τ : Tp} (x : τ ∈ Γ) (θ : Γ' ⊢c Γ)
             → (γ' : ⟦ Γ' ⟧c) → ⟦ subst-var θ x ⟧ γ' == (⟦ x ⟧v (⟦ θ  ⟧s γ'))
    interp-subst-var i0 θ γ' = Refl
    interp-subst-var (iS x) θ γ' = interp-subst-var x (fst θ) γ'

    interp-p· : {Γ : Ctx} {Γ' : Ctx} → (θ : Γ ⊇ Γ') → {τ : Tp} (γ' : _)
              → ⟦ p· θ {τ = τ} ⟧r γ' == ⟦ θ ⟧r (fst γ')
    interp-p· {Γ' = []} θ γ' = Refl
    interp-p· {Γ' = τ' :: Γ'} θ γ' = ap2 _,_ (interp-p· (fst θ) _) Refl

    interp-idr : {Γ : Ctx} (γ : _) → ⟦ idr {Γ} ⟧r γ == γ
    interp-idr {[]} γ = Refl
    interp-idr {x :: Γ} γ = ap (λ x₁ → x₁ , snd γ) (interp-idr (fst γ) ∘ interp-p· idr γ)

    interp-rename : {Γ' Γ : Ctx} {τ : Tp} (e : Γ ⊢ τ) (θ : Γ' ⊇ Γ)
          → (γ' : ⟦ Γ' ⟧c) → ⟦ rename θ e ⟧ γ' == (⟦ e ⟧ (⟦ θ  ⟧r γ'))
    interp-rename c θ γ' = Refl
    interp-rename (v x) θ γ' = interp-rename-var x θ γ'
    interp-rename (lam e) θ γ' = λ= (λ x → ap ⟦ e ⟧ (ap2 _,_ (interp-p· θ (γ' , x)) Refl) ∘ interp-rename e (addvar-ren θ) (γ' , x)) 
    interp-rename (app e e₁) θ γ' = ap2 (λ f x → f x) (interp-rename e θ γ') (interp-rename e₁ θ γ')
    interp-rename (foo e1 e2 p) Θ γ' = {!!} --interp-rename e1 Θ γ'

    interp-·rs : {Γ1 Γ2 Γ3 : Ctx} → (θ1 : Γ1 ⊇ Γ2) (θ2 : Γ2 ⊢c Γ3) (γ : _) → ⟦ θ1 ·rs θ2 ⟧s γ == ⟦ θ2 ⟧s (⟦ θ1 ⟧r γ)
    interp-·rs {Γ3 = []} θ1 θ2 γ = Refl
    interp-·rs {Γ3 = τ :: Γ3} θ1 (θ2 , e) γ = ap2 _,_ (interp-·rs θ1 θ2 γ) (interp-rename e θ1 γ)

    interp-subst : {Γ' Γ : Ctx} {τ : Tp} (e : Γ ⊢ τ) (θ : Γ' ⊢c Γ)
          → (γ' : ⟦ Γ' ⟧c) → ⟦ subst θ e ⟧ γ' == (⟦ e ⟧ (⟦ θ  ⟧s γ'))
    interp-subst c θ γ' = Refl
    interp-subst (v x) θ γ' = interp-subst-var x θ γ'
    interp-subst (lam e) θ γ' = λ= (λ x → ap (λ h → ⟦ e ⟧ (h , x)) (ap ⟦ θ ⟧s (interp-idr γ' ∘ interp-p· idr (γ' , x)) ∘ interp-·rs (p· idr) θ _) ∘ interp-subst e (addvar θ) (γ' , x))
    interp-subst (app e e₁) θ γ' = ap2 (λ f x → f x) (interp-subst e θ γ') (interp-subst e₁ θ γ')
    interp-subst (foo e1 e2 p) Θ γ' = {!!} --interp-subst e1 Θ γ'

    interp-·ss : {Γ1 Γ2 Γ3 : Ctx} → (θ1 : Γ1 ⊢c Γ2) (θ2 : Γ2 ⊢c Γ3) (γ : _) → ⟦ θ1 ·ss θ2 ⟧s γ == ⟦ θ2 ⟧s (⟦ θ1 ⟧s γ)
    interp-·ss {Γ3 = []} θ1 θ2 γ = Refl
    interp-·ss {Γ3 = τ :: Γ3} θ1 (θ2 , e) γ = ap2 _,_ (interp-·ss θ1 θ2 γ) (interp-subst e θ1 γ)

    interp-ids : ∀ {Γ} (γ : _) → ⟦ ids {Γ} ⟧s γ == γ
    interp-ids {[]} γ = Refl
    interp-ids {τ :: Γ} γ = ap (λ x → x , snd γ) (((interp-idr (fst γ) ∘ interp-p· idr γ) ∘ interp-ids (⟦ p ⟧r γ)) ∘ interp-·rs p ids γ)

    sound (CongApp D D') γ = ap2 (λ f x → f x) (sound D γ) (sound D' γ)
    sound (CongLam D) γ = λ= (λ x → sound D (γ , x))
    sound {e' = e'} SubstId γ = ap ⟦ e' ⟧ (interp-ids γ) ∘ interp-subst e' ids γ
    sound (SubstComp {θ' = θ'}{θ}{e = e}) γ = ((! (interp-subst e _ γ) ∘ ap ⟦ e ⟧ (! (interp-·ss θ' θ γ))) ∘ interp-subst e θ (⟦ θ' ⟧s γ)) ∘ interp-subst (subst θ e) θ' γ
    sound (Stepβ {e = e} {e1 = e1}) γ = ! (interp-subst e (ids , e1) γ) ∘ ap (λ x → ⟦ e ⟧ (x , ⟦ e1 ⟧ γ)) (! (interp-ids γ))
    sound Refl γ = Refl
    sound (Trans D D₁) γ = sound D₁ γ ∘ sound D γ
    sound {Γ'} (SubstCong {Γ} {τ} {Θ} {e1} {e2} D) γ = {!!} --(! (interp-subst e2 Θ γ) ∘ sound D (⟦ Θ ⟧s γ)) ∘ interp-subst e1 Θ γ
    sound {Γ'} (RenCong {Γ} {τ} {ρ} {e1} {e2} D) γ = {!!} --(! (interp-rename e2 ρ γ) ∘ sound D (⟦ ρ ⟧r γ)) ∘ interp-rename e1 ρ γ

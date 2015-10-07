open import Preliminaries

{-
strong normalization for STLC
adapted from OPLSS
edward yang's proof of weak normalization is also helpful
-}

module STLC where

  data Tp : Set where
    b : Tp -- uninterpreted base type
    _⇒_ : Tp → Tp → Tp

  Ctx = List Tp

  data _∈_ : Tp → List Tp → Set where
    i0 : ∀ {Γ τ} → τ ∈ (τ :: Γ)
    iS : ∀ {Γ τ τ1} → τ ∈ Γ → τ ∈ (τ1 :: Γ)

  infixr 10 _⇒_
  infixr 8 _|-_

  data _|-_ : Ctx → Tp → Set where
    c   : ∀ {Γ} → Γ |- b -- some constant of the base type
    v   : ∀ {Γ τ} 
        → τ ∈ Γ
        → Γ |- τ
    lam : ∀ {Γ τ1 τ2} → (τ1 :: Γ) |- τ2 → Γ |- τ1 ⇒ τ2
    app : ∀ {Γ τ1 τ2} → Γ |- τ1 ⇒ τ2 → Γ |- τ1 → Γ |- τ2

  data val :  {τ : Tp} → [] |- τ → Set where
    c-isval : val c
    lam-isval : {τ₁ τ₂ : Tp} {e : τ₁ :: [] |- τ₂} → val (lam e)

  module RenSubst where

    rctx : Ctx → Ctx → Set
    rctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → τ ∈ Γ

    r-extend : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) (τ :: Γ')
    r-extend ρ i0 = i0
    r-extend ρ (iS i) = iS (ρ i)

    ren : ∀ {Γ Γ' τ} → Γ' |- τ → rctx Γ Γ' → Γ |- τ
    ren c ρ = c
    ren (v x) ρ = v (ρ x)
    ren (lam e) ρ = lam (ren e (r-extend ρ))
    ren (app e e₁) ρ = app (ren e ρ) (ren e₁ ρ)

    sctx : Ctx → Ctx → Set
    sctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → Γ |- τ

    wkn : ∀ {Γ τ1 τ2} → Γ |- τ2 → (τ1 :: Γ) |- τ2
    wkn e = ren e iS

    s-extend : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) (τ :: Γ')
    s-extend Θ i0 = v i0
    s-extend Θ (iS x) = wkn (Θ x)

    subst : ∀ {Γ Γ' τ} → Γ' |- τ → sctx Γ Γ' → Γ |- τ
    subst c Θ = c
    subst (v x) Θ = Θ x
    subst (lam e) Θ = lam (subst e (s-extend Θ))
    subst (app e e₁) Θ = app (subst e Θ) (subst e₁ Θ)

    ids : ∀ {Γ} → sctx Γ Γ
    ids x = v x

    add1 : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ |- τ → sctx Γ (τ :: Γ')
    add1 Θ e i0 = e
    add1 Θ e (iS i) = Θ i

    q : ∀ {Γ τ} → Γ |- τ → sctx Γ (τ :: Γ)
    q e = add1 ids e

    subst1 : {τ τ0 : Tp} → [] |- τ0 → (τ0 :: []) |- τ → [] |- τ
    subst1 e0 e = subst e (add1 ids e0)

  open RenSubst

  module OpSem where
    -- step relation
    data _↦_ : {τ : Tp} → [] |- τ → [] |- τ → Set where
      Step/app : {τ1 τ2 : Tp} {e1 e1' : [] |- τ1 ⇒ τ2} {e2 : [] |- τ1}
               → e1 ↦ e1'
               → app e1 e2 ↦ app e1' e2
      Step/β : {τ1 τ2 : Tp} {e : τ1 :: [] |- τ2} {e1 : [] |- τ1}
             → app (lam e) e1 ↦ subst1 e1 e

    -- reflexive/transitive closure
    data _↦*_ : {τ : Tp} → [] |- τ → [] |- τ → Set where
      Done : {τ : Tp} {e : [] |- τ} → e ↦* e
      Step : {τ : Tp} {e1 e2 e3 : [] |- τ} 
           → e1 ↦ e2  →  e2 ↦* e3
           → e1 ↦* e3

    _⇣_ : {τ : Tp} → [] |- τ → [] |- τ → Set
    e ⇣ k = val k × e ↦* k

    _⇣ : {τ : Tp} → [] |- τ → Set
    e ⇣ = Σ (λ k → e ⇣ k)

  module StrongNormalization where
    open OpSem

    -- definition of SN from
    -- http://www.cs.cornell.edu/courses/cs6110/2013sp/lectures/lec33-sp13.pdf
    -- from my understanding: if e is a well-typed term, then e normalizes to a value
    SN : (τ : Tp) → [] |- τ → Set
    -- SN_b(e) iff e ⇣
    SN b e = e ⇣
    -- SN_(t1->t2)(e) iff e ⇣ and ∀ e', SN_t1(e') -> SN_t2(app e e')
    SN (t1 ⇒ t2) e = e ⇣ × Σ (λ e' → SN t1 e' → SN t2 (app e e'))

    SNc : (Γ : Ctx) → sctx [] Γ → Set
    SNc [] Θ = Unit
    SNc (τ :: Γ) Θ = SNc Γ {!!} × SN τ (Θ i0)

    head-expand : (τ : Tp) {e e' : [] |- τ} → e ↦ e' → SN τ e' → SN τ e
    head-expand b e↦e' (e₁ , e₁-isval , e'↦*e₁) = e₁ , (e₁-isval , Step e↦e' e'↦*e₁)
    head-expand (e ⇒ e₁) e↦e' ((body , body-isval , e'↦*body) , k , sn) = (body , (body-isval , Step e↦e' e'↦*body)) , (k , {!!}) 

--(body , (body-isval , (Step e↦e' e'↦*body))) , (k , {!!})

    fund : {Γ : Ctx} {τ : Tp} {Θ : sctx [] Γ} 
         → (e : Γ |- τ)
         → SNc Γ Θ
         → SN τ (subst e Θ)
    fund c snc = c , (c-isval , Done)
    fund (v i0) snc = snd snc
    fund (v (iS x)) snc = fund (v x) (fst snc)
    fund {_} {τ1 ⇒ τ2} {Θ} (lam e) snc = (subst (lam e) Θ , (lam-isval , Done)) , ({!!} , {!!})
    fund (app e1 e2) snc with fund e1 snc
    ... | (v1 , v1-isval , e1↦*v1) , v2 , IH = {!!}

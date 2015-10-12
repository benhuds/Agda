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

  module Semantics (B : Set) (elB : B)  where

    -- map STLC types to Agda types
    [_]t : Tp → Set
    [ b ]t = B
    [ τ1 ⇒ τ2 ]t = [ τ1 ]t → [ τ2 ]t

    [_]c : Ctx → Set
    [ [] ]c = Unit
    [ τ :: Γ ]c = [ Γ ]c × [ τ ]t

    -- interpretation of terms
    [_] : {Γ : Ctx} {τ : Tp} → Γ |- τ → [ Γ ]c → [ τ ]t
    [ c ]  γ = elB
    [ v i0 ] γ = snd γ
    [ v (iS i) ] γ = [ v i ] (fst γ)
    [  lam e ] γ x = [ e ] (γ , x)
    [ app e1 e2 ] γ = [ e1 ] γ ([ e2 ] γ)

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

    lem3' : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ |- τ → sctx Γ (τ :: Γ')
    lem3' Θ e i0 = e
    lem3' Θ e (iS i) = Θ i

    ids : ∀ {Γ} → sctx Γ Γ
    ids x = v x

      --lem3
    q : ∀ {Γ τ} → Γ |- τ → sctx Γ (τ :: Γ)
    q e = lem3' ids e

    svar : ∀ {Γ1 Γ2 τ} → sctx Γ1 Γ2 → τ ∈ Γ2 → Γ1 |- τ
    svar Θ i = q (Θ i) i0

    subst : ∀ {Γ Γ' τ} → Γ' |- τ → sctx Γ Γ' → Γ |- τ
    subst c Θ = c
    subst (v x) Θ = Θ x
    subst (lam e) Θ = lam (subst e (s-extend Θ))
    subst (app e e₁) Θ = app (subst e Θ) (subst e₁ Θ)

    svar-id : ∀ {Γ τ} → (x : τ ∈ Γ) → v x == svar ids x
    svar-id = λ x → Refl

    subst-id : ∀ {Γ τ} (e : Γ |- τ) → e == subst e ids
    subst-id c = Refl
    subst-id (v x) = svar-id x
    subst-id (lam e) = {!!}
    subst-id (app e e₁) = ap2 app (subst-id e) (subst-id e₁)

    add1 : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ |- τ → sctx Γ (τ :: Γ')
    add1 Θ e i0 = e
    add1 Θ e (iS i) = Θ i

    subst1 : ∀ {Γ τ τ'} → Γ |- τ' → (τ' :: Γ) |- τ → Γ |- τ
    subst1 e0 e = subst e (add1 ids e0)

    throw : ∀ {Γ Γ' τ} → sctx Γ (τ :: Γ') → sctx Γ Γ'
    throw Θ x = Θ (iS x)

    throw-eq-lemma : ∀ {Γ Γ' τ τ'} → (Θ : sctx Γ (τ :: Γ')) (Θ' : sctx Γ Γ') (x : τ' ∈ Γ') → _==_ (throw Θ x) (Θ' x)
    throw-eq-lemma Θ Θ' x = {!!} --i'm thinking i have to do some sort of equation chain
-- wts throw Θ x = Θ (iS x) == Θ' x

    throw-eq2 : ∀ {Γ Γ' τ} → (Θ : sctx Γ Γ') → _==_ {_} {_} (throw (s-extend Θ)) {!throw (s-extend Θ)!}
    throw-eq2 = {!!}

    throw-eq : ∀ {Γ Γ' τ} → (Θ : sctx Γ (τ :: Γ')) (Θ' : sctx Γ Γ') → _==_ {_} {sctx Γ Γ'} (throw Θ) Θ'
    throw-eq Θ Θ' = λ=i (λ τ → λ= (λ x → throw-eq-lemma Θ Θ' x))

    throw-svar : ∀ {Γ Γ' τ τ'} (Θ : sctx Γ (τ :: Γ')) (Θ' : sctx Γ Γ') (x : τ' ∈ Γ') → svar (throw Θ) x == svar Θ' x
    throw-svar Θ Θ' x = throw-eq-lemma Θ Θ' x

    throw-subst : ∀ {Γ Γ' τ τ'} (Θ : sctx Γ (τ :: Γ')) (Θ' : sctx Γ Γ') (e : Γ' |- τ') (x : τ' ∈ Γ') → subst e (throw Θ) == Θ (iS x)
    throw-subst Θ Θ' e x = {!!}

    throw-is-ok : ∀ {Γ Γ' τ τ'} (Θ : sctx Γ (τ :: Γ')) (Θ' : sctx Γ Γ') (e : Γ' |- τ') → subst e (throw Θ) == subst e Θ'
    throw-is-ok Θ Θ' c = Refl
    throw-is-ok Θ Θ' (v x) = throw-svar Θ Θ' x
    throw-is-ok Θ Θ' (lam e) = ap lam (ap (subst e) (ap s-extend (throw-eq Θ Θ')))
    throw-is-ok Θ Θ' (app e e₁) = ap2 app (ap (subst e) (throw-eq Θ Θ')) (ap (subst e₁) (throw-eq Θ Θ'))

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

    -- a well-typed expression e evals to k if k is a value and
    -- there is some sequence of eval steps from e to k
    -- type \d
    _⇓_ : {τ : Tp} → [] |- τ → [] |- τ → Set
    e ⇓ k = val k × e ↦* k

    -- classical notion of strong normalization:
    -- e is strongly normalizing if there is no infinite
    -- reduction sequence e → e' → e'' → ...
    -- i.e. there's some value k which e eventually evaluates to
    _⇓ : {τ : Tp} → [] |- τ → Set
    e ⇓ = Σ (λ k → e ⇓ k)

  module StrongNormalization where
    open OpSem

    -- definition of SN from
    -- http://www.cs.cornell.edu/courses/cs6110/2013sp/lectures/lec33-sp13.pdf
    -- if e is a well-typed term, then e is strongly normalizing
    SN : (τ : Tp) → [] |- τ → Set
    -- SN_b(e) iff e ⇣
    SN b e = e ⇓
    -- SN_(t1->t2)(e) iff e ⇣ and ∀ e', SN_t1(e') -> SN_t2(app e e')
    SN (t1 ⇒ t2) e = e ⇓ × Σ (λ e' → SN t1 e' → SN t2 (app e e'))

    -- how to describe?
    SNc : (Γ : Ctx) → sctx [] Γ → Set
    SNc [] Θ = Unit
    SNc (τ :: Γ) Θ = SNc Γ (throw Θ) × SN τ (Θ i0)

    -- need a new definition for γ|=Γ. can i do it without induction on Γ?
    SNc2 : (Γ : Ctx) → sctx [] Γ → Set
    SNc2 Γ Θ = Σ (λ x → x ∈ Γ × SN x (Θ {!!}))

    -- step relation is closed under head expansion
    head-expand : (τ : Tp) {e e' : [] |- τ} → e ↦ e' → SN τ e' → SN τ e
    head-expand b e↦e' (e₁ , e₁-isval , e'↦*e₁) = e₁ , (e₁-isval , Step e↦e' e'↦*e₁)
    head-expand (e ⇒ e₁) e↦e' ((body , body-isval , e'↦*body) , k , sn) =
                   (body , (body-isval , Step e↦e' e'↦*body)) , (k , (λ x → head-expand _ (Step/app e↦e') (sn x)))

    -- refl/trans closure of step relation is closed under head expansion
    head-expand* : {τ : Tp} {e e' : [] |- τ} → e ↦* e' → SN τ e' → SN τ e
    head-expand* Done sn = sn
    head-expand* (Step x steps) sn = head-expand _ x (head-expand* steps sn)

    Step/app*  :{τ1 τ2 : Tp} {e e' : [] |- τ1 ⇒ τ2} {e1 : [] |- τ1}
             → e ↦* e'
             → (app e e1) ↦* (app e' e1)
    Step/app* Done = Done
    Step/app* (Step s ss) = (Step (Step/app s) (Step/app* ss))

    Step' : {τ : Tp} {e1 e2 e3 : [] |- τ} 
           → e1 ↦* e2  →  e2 ↦ e3
           → e1 ↦* e3
    Step' Done s = Step s Done
    Step' (Step s ss) s' = Step s (Step' ss s')

    -- fundamental theorem
    fund : {Γ : Ctx} {τ : Tp} {Θ : sctx [] Γ} 
         → (e : Γ |- τ)
         → SNc Γ Θ
         → SN τ (subst e Θ)
    fund c snc = c , (c-isval , Done)
    fund (v i0) snc = snd snc
    fund (v (iS x)) snc = fund (v x) (fst snc)
    fund {_} {τ1 ⇒ τ2} {Θ} (lam e) snc = (subst (lam e) Θ , (lam-isval , Done)) , ({!!} , {!!})
    fund (app e1 e2) snc with fund e1 snc
    ... | (v1 , v1-isval , e1↦*v1) , v2 , IH = head-expand* (Step' (Step/app* e1↦*v1) {!Step/β!}) {!!}

    corollary : {τ : Tp} → (e : [] |- τ) → e ⇓
    corollary e = transport (λ e' → e' ⇓) (! (subst-id e)) {!!}

{- Name: Bowornmet (Ben) Hudson

-- define the source language from the paper

-}

open import Preliminaries
open import Preorder-withmax

module Proofs where

  -- define the source language from the paper
  -- we want to focus on arrow, cross, and nat types
  data Tp : Set where
    unit : Tp
    nat : Tp
    susp : Tp → Tp
    _->s_ : Tp → Tp → Tp
    _×s_ : Tp → Tp → Tp

  data Cost : Set where
    0c : Cost
    1c : Cost
    _+c_ : Cost → Cost → Cost

  data Equals0c : Cost → Set where
    Eq0-0c : Equals0c 0c
    Eq0-+c : ∀ {c c'} → Equals0c c → Equals0c c' → Equals0c (c +c c')

  -- represent a context as a list of types
  Ctx = List Tp

  -- de Bruijn indices (for free variables)
  data _∈_ : Tp → Ctx → Set where
    i0 : ∀ {Γ τ}
       → τ ∈ (τ :: Γ)
    iS : ∀ {Γ τ τ1}
       → τ ∈ Γ
       → τ ∈ (τ1 :: Γ)

  data _|-_ : Ctx → Tp → Set where
    unit : ∀ {Γ}
         → Γ |- unit
    var : ∀ {Γ τ}
        → τ ∈ Γ
        → Γ |- τ
    z : ∀ {Γ}
      → Γ |- nat
    suc : ∀ {Γ}
        → (e : Γ |- nat)        
        → Γ |- nat
    rec : ∀ {Γ τ}
        → Γ |- nat
        → Γ |- τ
        → (nat :: (susp τ :: Γ)) |- τ
        → Γ |- τ
    lam : ∀ {Γ τ ρ}
        → (ρ :: Γ) |- τ
        → Γ |- (ρ ->s τ)
    app : ∀ {Γ τ1 τ2}
        → Γ |- (τ2 ->s τ1)
        → Γ |- τ2
        → Γ |- τ1
    prod : ∀ {Γ τ1 τ2}
         → Γ |- τ1
         → Γ |- τ2
         → Γ |- (τ1 ×s τ2)
    l-proj : ∀ {Γ τ1 τ2}
           → Γ |- (τ1 ×s τ2)
           → Γ |- τ1
    r-proj : ∀ {Γ τ1 τ2}
           → Γ |- (τ1 ×s τ2)
           → Γ |- τ2
    -- include split, delay/susp/force instead of usual elim rules for products
    delay : ∀ {Γ τ}
          → Γ |- τ
          → Γ |- susp τ
    force : ∀ {Γ τ}
          → Γ |- susp τ
          → Γ |- τ
    split : ∀ {Γ τ τ1 τ2}
          → Γ |- (τ1 ×s τ2)
          → (τ1 :: (τ2 :: Γ)) |- τ
          → Γ |- τ

------weakening and substitution lemmas

 -- renaming function
  rctx : Ctx → Ctx → Set
  rctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → τ ∈ Γ

  -- re: transferring variables in contexts
  lem1 : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) (τ :: Γ')
  lem1 d i0 = i0
  lem1 d (iS x) = iS (d x)

  -- renaming lemma
  ren : ∀ {Γ Γ' τ} → Γ' |- τ → rctx Γ Γ' → Γ |- τ
  ren unit d = unit
  ren (var x) d = var (d x)
  ren z d = z
  ren (suc e) d = suc (ren e d)
  ren (rec e e0 e1) d = rec (ren e d) (ren e0 d) (ren e1 (lem1 (lem1 d)))
  ren (lam e) d = lam (ren e (lem1 d))
  ren (app e1 e2) d = app (ren e1 d) (ren e2 d)
  ren (prod e1 e2) d = prod (ren e1 d) (ren e2 d)
  ren (l-proj e) d = l-proj (ren e d)
  ren (r-proj e) d = r-proj (ren e d)
  ren (delay e) d = delay (ren e d)
  ren (force e) d = force (ren e d)
  ren (split e e1) d = split (ren e d) (ren e1 (lem1 (lem1 d)))

  -- substitution
  sctx : Ctx → Ctx → Set
  sctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → Γ |- τ

  -- weakening a context
  wkn : ∀ {Γ τ1 τ2} → Γ |- τ2 → (τ1 :: Γ) |- τ2
  wkn e = ren e iS

  -- weakening also works with substitution
  wkn-s : ∀ {Γ τ1 Γ'} → sctx Γ Γ' → sctx (τ1 :: Γ) Γ'
  wkn-s d = λ f → wkn (d f)

  wkn-r : ∀ {Γ τ1 Γ'} → rctx Γ Γ' → rctx (τ1 :: Γ) Γ'
  wkn-r d = λ x → iS (d x)

  -- lem2 (need a lemma for subst like we did for renaming)
  lem2 : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) (τ :: Γ')
  lem2 d i0 = var i0
  lem2 d (iS i) = wkn (d i)

  -- another substitution lemma
  lem3 : ∀ {Γ τ} → Γ |- τ → sctx Γ (τ :: Γ)
  lem3 e i0 = e
  lem3 e (iS i) = var i

  lem3' : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ |- τ → sctx Γ (τ :: Γ')
  lem3' Θ e i0 = e
  lem3' Θ e (iS i) = Θ i

  -- one final lemma needed for the last stepping rule. Thank you Professor Licata!
  lem4 : ∀ {Γ τ1 τ2} → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ))
  lem4 e1 e2 i0 = e1
  lem4 e1 e2 (iS i0) = e2
  lem4 e1 e2 (iS (iS i)) = var i

  lem4' : ∀ {Γ Γ' τ1 τ2} → sctx Γ Γ' → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ'))
  lem4' Θ a b i0 = a
  lem4' Θ a b (iS i0) = b
  lem4' Θ a b (iS (iS i)) = Θ i

  lem5 : ∀ {Γ τ1 τ2} → Γ |- (τ1 ×s τ2) → sctx Γ ((τ1 ×s τ2) :: (τ1 :: (τ2 :: Γ)))
  lem5 e i0 = e
  lem5 e (iS i0) = l-proj e
  lem5 e (iS (iS i0)) = r-proj e
  lem5 e (iS (iS (iS i))) = var i

  -- the 'real' substitution lemma (if (x : τ') :: Γ |- (e : τ) and Γ |- (e : τ') , then Γ |- e[x -> e'] : τ)
  subst : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ' |- τ → Γ |- τ
  subst d unit = unit
  subst d (var x) = d x
  subst d z = z
  subst d (suc x) = suc (subst d x)
  subst d (rec e e0 e1) = rec (subst d e) (subst d e0) (subst (lem2 (lem2 d)) e1)
  subst d (lam e) = lam (subst (lem2 d) e)
  subst d (app e1 e2) = app (subst d e1) (subst d e2)
  subst d (prod e1 e2) = prod (subst d e1) (subst d e2)
  subst d (l-proj e) = l-proj (subst d e)
  subst d (r-proj e) = r-proj (subst d e)
  subst d (delay e) = delay (subst d e)
  subst d (force e) = force (subst d e)
  subst d (split e e1) = split (subst d e) (subst (lem2 (lem2 d)) e1)

  subst-compose : ∀ {Γ Γ' τ τ1} (Θ : sctx Γ Γ') (v : Γ |- τ) (e : (τ :: Γ' |- τ1) )
                → subst (lem3 v) (subst (lem2 Θ) e) == subst (lem3' Θ v) e
  subst-compose Θ unit e = {!!}
  subst-compose Θ (var x) e = {!!}
  subst-compose Θ z e = {!!}
  subst-compose Θ (suc v) e = {!!}
  subst-compose Θ (rec v v₁ v₂) e = {!!}
  subst-compose Θ (lam v) e = {!!}
  subst-compose Θ (app v v₁) e = {!!}
  subst-compose Θ (prod v v₁) e = {!!}
  subst-compose Θ (l-proj v) e = {!!}
  subst-compose Θ (r-proj v) e = {!!}
  subst-compose Θ (delay v) e = {!!}
  subst-compose Θ (force v) e = {!!}
  subst-compose Θ (split v v₁) e = {!!}

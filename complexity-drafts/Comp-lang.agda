{- Name: Bowornmet (Ben) Hudson

-- define the complexity language from the paper

-}

open import Preliminaries
open import Preorder-withmax

module Comp-lang where

  -- define the complexity language from the paper
  -- we want to focus on arrow, cross, and nat types
  -- do I need unit types?
  data CTp : Set where
    unit : CTp
    nat : CTp
    _->c_ : CTp → CTp → CTp
    _×c_ : CTp → CTp → CTp
    C : CTp

  -- represent a context as a list of types
  Ctx = List CTp

  -- de Bruijn indices (for free variables)
  data _∈_ : CTp → Ctx → Set where
    i0 : ∀ {Γ τ}
       → τ ∈ (τ :: Γ)
    iS : ∀ {Γ τ τ1}
       → τ ∈ Γ
       → τ ∈ (τ1 :: Γ)

  data _|-_ : Ctx → CTp → Set where
    unit : ∀ {Γ}
         → Γ |- unit
    0C : ∀ {Γ}
       → Γ |- C
    1C : ∀ {Γ}
       → Γ |- C
    plusC : ∀ {Γ}
         → Γ |- C
         → Γ |- C
         → Γ |- C
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
        → (nat :: (τ :: Γ)) |- τ
        → Γ |- τ
    lam : ∀ {Γ τ ρ}
        → (ρ :: Γ) |- τ
        → Γ |- (ρ ->c τ)
    app : ∀ {Γ τ1 τ2}
        → Γ |- (τ2 ->c τ1)
        → Γ |- τ2
        → Γ |- τ1
    prod : ∀ {Γ τ1 τ2}
         → Γ |- τ1
         → Γ |- τ2
         → Γ |- (τ1 ×c τ2)
    l-proj : ∀ {Γ τ1 τ2}
           → Γ |- (τ1 ×c τ2)
           → Γ |- τ1
    r-proj : ∀ {Γ τ1 τ2}
           → Γ |- (τ1 ×c τ2)
           → Γ |- τ2

  _+C_ : ∀ {Γ τ} → Γ |- C  → Γ |- (C ×c τ)→ Γ |- (C ×c τ)
  c +C e = prod (plusC c (l-proj e)) (r-proj e)

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
  ren 0C d = 0C
  ren 1C d = 1C
  ren (plusC e1 e2) d = plusC (ren e1 d) (ren e2 d)
  ren (var x) d = var (d x)
  ren z d = z
  ren (suc e) d = suc (ren e d)
  ren (rec e e0 e1) d = rec (ren e d) (ren e0 d) (ren e1 (lem1 (lem1 d)))
  ren (lam e) d = lam (ren e (lem1 d))
  ren (app e1 e2) d = app (ren e1 d) (ren e2 d)
  ren (prod e1 e2) d = prod (ren e1 d) (ren e2 d)
  ren (l-proj e) d = l-proj (ren e d)
  ren (r-proj e) d = r-proj (ren e d)

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

  -- the 'real' substitution lemma (if (x : τ') :: Γ |- (e : τ) and Γ |- (e : τ') , then Γ |- e[x -> e'] : τ)
  subst : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ' |- τ → Γ |- τ
  subst d unit = unit
  subst d 0C = 0C
  subst d 1C = 1C
  subst d (plusC e1 e2) = plusC (subst d e1) (subst d e2)
  subst d (var x) = d x
  subst d z = z
  subst d (suc x) = suc (subst d x)
  subst d (rec e e0 e1) = rec (subst d e) (subst d e0) (subst (lem2 (lem2 d)) e1)
  subst d (lam e) = lam (subst (lem2 d) e)
  subst d (app e1 e2) = app (subst d e1) (subst d e2)
  subst d (prod e1 e2) = prod (subst d e1) (subst d e2)
  subst d (l-proj e) = l-proj (subst d e)
  subst d (r-proj e) = r-proj (subst d e)

  postulate
    subst-compose : ∀ {Γ Γ' τ τ1} (Θ : sctx Γ Γ') (v : Γ |- τ) (e : (τ :: Γ' |- τ1) )
                  → subst (lem3 v) (subst (lem2 Θ) e) == subst (lem3' Θ v) e

  postulate
    subst-compose2 : ∀ {Γ Γ' τ} (Θ : sctx Γ Γ') (n : Γ |- nat) (e1 : Γ' |- τ) (e2 : (nat :: (τ :: Γ')) |- τ)
                  →  subst (lem4 n (rec n (subst Θ e1) (subst (lem2 (lem2 Θ)) e2))) (subst (lem2 (lem2 Θ)) e2) ==
                     subst (lem4' Θ n (rec n (subst Θ e1) (subst (lem2 (lem2 Θ)) e2))) e2

  postulate
    subst-compose3 : ∀ {Γ Γ' τ τ1 τ2} (Θ : sctx Γ Γ') (e1 : (τ1 :: (τ2 :: Γ')) |- τ) (v1 : Γ' |- τ1) (v2 : Γ' |- τ2)
                   → subst Θ (subst (lem4 v1 v2) e1) == subst (lem4' Θ (subst Θ v1) (subst Θ v2)) e1

  postulate
    subst-compose4 : ∀ {Γ Γ' τ} (Θ : sctx Γ Γ') (v' : Γ |- nat) (r : Γ |- τ) (e2 : (nat :: (τ :: Γ')) |- τ)
                   → subst (lem4 v' r) (subst (lem2 (lem2 Θ)) e2) == subst (lem4' Θ v' r) e2

-------

  -- define 'stepping' as a datatype (fig. 1 of proof)
  data _≤s_ : ∀ {Γ T} → Γ |- T → Γ |- T → Set where
    refl-s : ∀ {Γ T}
           → {e : Γ |- T}
           → e ≤s e
    trans-s : ∀ {Γ T}
            → {e e' e'' : Γ |- T}
            → e ≤s e' → e' ≤s e''
            → e ≤s e''
    plus-s : ∀ {Γ}
           → {e1 e2 n1 n2 : Γ |- C}
           → e1 ≤s n1 → e2 ≤s n2
           → (plusC e1 e2) ≤s (plusC n1 n2)
    cong-refl : ∀ {Γ τ} {e e' : Γ |- τ} → e == e' → e ≤s e'
    +-unit-l : ∀ {Γ} {e : Γ |- C} → (plusC 0C e) ≤s e
    +-unit-l' : ∀ {Γ} {e : Γ |- C} → e ≤s (plusC 0C e) 
    +-unit-r : ∀ {Γ} {e : Γ |- C} → (plusC e 0C) ≤s e
    +-unit-r' : ∀ {Γ} {e : Γ |- C} → e ≤s (plusC e 0C) 
    +-assoc : ∀ {Γ} {e1 e2 e3 : Γ |- C} → (plusC e1 (plusC e2 e3)) ≤s (plusC (plusC e1 e2) e3)
    +-assoc' : ∀ {Γ} {e1 e2 e3 : Γ |- C} → (plusC e1 (plusC e2 e3)) ≤s (plusC (plusC e1 e2) e3)
    refl-+ : ∀ {Γ} {e0 e1 : Γ |- C} → (plusC e0 e1) ≤s (plusC e1 e0)
    cong-+ : ∀ {Γ} {e0 e1 e0' e1' : Γ |- C} → e0 ≤s e0' → e1 ≤s e1' → (plusC e0 e1) ≤s (plusC e0' e1')    
    cong-lproj : ∀ {Γ τ τ'} {e e' : Γ |- (τ ×c τ')} → e ≤s e' → (l-proj e) ≤s (l-proj e')    
    cong-rproj : ∀ {Γ τ τ'} {e e' : Γ |- (τ ×c τ')} → e ≤s e' → (r-proj e) ≤s (r-proj e')
    cong-app   : ∀ {Γ τ τ'} {e e' : Γ |- (τ ->c τ')} {e1 : Γ |- τ} → e ≤s e' → (app e e1) ≤s (app e' e1)
    cong-rec : ∀ {Γ τ} {e e' : Γ |- nat} {e0 : Γ |- τ} {e1 : (nat :: (τ :: Γ)) |- τ}
             → e ≤s e'
             → rec e e0 e1 ≤s rec e' e0 e1
    lam-s : ∀ {Γ T T'}
          → {e : (T :: Γ) |- T'}
          → {e2 : Γ |- T}
          → subst (lem3 e2) e ≤s app (lam e) e2
    l-proj-s : ∀ {Γ T1 T2}
             → {e1 : Γ |- T1}  {e2 : Γ |- T2}
             → e1 ≤s (l-proj (prod e1 e2))
    r-proj-s : ∀ {Γ T1 T2}
             → {e1 : Γ |- T1} → {e2 : Γ |- T2}
             → e2 ≤s (r-proj (prod e1 e2))
    rec-steps-s : ∀ {Γ T}
                → {e : Γ |- nat}
                → {e0 : Γ |- T}
                → {e1 : (nat :: (T :: Γ)) |- T}
                → subst (lem4 e (rec e e0 e1)) e1 ≤s (rec (suc e) e0 e1)
    rec-steps-z : ∀ {Γ T}
                → {e0 : Γ |- T}
                → {e1 : (nat :: (T :: Γ)) |- T}
                → e0 ≤s (rec z e0 e1)

  _trans_ : ∀ {Γ T}
            → {e e' e'' : Γ |- T}
            → e ≤s e' → e' ≤s e''
            → e ≤s e''
  _trans_ = trans-s
  infixr 10 _trans_

-------

  -- interpret complexity types as preorders
  [_]t : CTp → PREORDER
  [ unit ]t = unit-p
  [ nat ]t = Nat , nat-p
  [ A ->c B ]t = [ A ]t ->p [ B ]t
  [ A ×c B ]t = [ A ]t ×p [ B ]t
  [ C ]t = Nat , nat-p
  
  -- interpret contexts as preorders
  [_]c : Ctx → PREORDER
  [ [] ]c = unit-p
  [ τ :: Γ ]c = [ τ ]t ×p [ Γ ]c

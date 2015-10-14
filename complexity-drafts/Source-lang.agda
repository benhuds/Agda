{- Name: Bowornmet (Ben) Hudson

-- define the source language from the paper

-}

open import Preliminaries
open import Preorder-withmax

module Source-lang where

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

  ids-2 : ∀ {Γ τ} → Γ |- τ → sctx Γ Γ → Γ |- τ
  ids-2 e Θ = e

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

  s-comp1 : ∀ {Γ Γ' Γ''} → sctx Γ Γ' → sctx Γ'' Γ → sctx Γ'' Γ'
  s-comp1 Θ Θ' = subst Θ' o Θ

  postulate
    subst-compose : ∀ {Γ Γ' τ τ1} (Θ : sctx Γ Γ') (v : Γ |- τ) (e : (τ :: Γ' |- τ1) )
                  → subst (lem3 v) (subst (lem2 Θ) e) == subst (lem3' Θ v) e
    --subst-compose {Γ} {_} Θ v e = {!!}

  postulate
    subst-compose2 : ∀ {Γ Γ' τ} (Θ : sctx Γ Γ') (n : Γ |- nat) (e1 : Γ' |- τ) (e2 : (nat :: (susp τ :: Γ')) |- τ)
                  →  subst (lem4 n (delay (rec n (subst Θ e1) (subst (lem2 (lem2 Θ)) e2)))) (subst (lem2 (lem2 Θ)) e2) ==
                     subst (lem4' Θ n (delay (rec n (subst Θ e1) (subst (lem2 (lem2 Θ)) e2)))) e2

  postulate
    subst-compose3 : ∀ {Γ Γ' τ τ1 τ2} (Θ : sctx Γ Γ') (e1 : (τ1 :: (τ2 :: Γ')) |- τ) (v1 : Γ |- τ1) (v2 : Γ |- τ2)
                   → subst (lem4 v1 v2) (subst (lem2 (lem2 Θ)) e1) == subst (lem4' Θ v1 v2) e1

  postulate
    subst-compose4 : ∀ {Γ Γ' τ} (Θ : sctx Γ Γ') (v' : Γ |- nat) (r : Γ |- susp τ) (e2 : (nat :: (susp τ :: Γ')) |- τ)
                   → subst (lem4 v' r) (subst (lem2 (lem2 Θ)) e2) == subst (lem4' Θ v' r) e2

-------

  data val : ∀ {τ} → [] |- τ → Set where
    z-isval : val z
    suc-isval : (e : [] |- nat) → (val e)
              → val (suc e)
    pair-isval : ∀ {τ1 τ2} (e1 : [] |- τ1) → (e2 : [] |- τ2)
               → val e1 → val e2
               → val (prod e1 e2)
    lam-isval : ∀ {ρ τ} (e : (ρ :: []) |- τ)
              → val (lam e)
    unit-isval : val unit
    delay-isval : ∀ {τ} (e : [] |- τ) → val (delay e)

  mutual
    -- define evals (e : source exp) (v : value) (c : nat)
    -- analogous to "e evaluates to v in c steps"
    -- see figure 4 of paper
    data evals : {τ : Tp} → [] |- τ → [] |- τ → Cost → Set where
      pair-evals : ∀ {n1 n2}
                 → {τ1 τ2 : Tp} {e1 v1 : [] |- τ1} {e2 v2 : [] |- τ2}
                 → evals e1 v1 n1
                 → evals e2 v2 n2
                 → evals (prod e1 e2) (prod v1 v2) (n1 +c n2)
      lam-evals : ∀ {ρ τ} {e : (ρ :: []) |- τ} 
                → evals (lam e) (lam e) 0c
      app-evals : ∀ {n0 n1 n}
               → {τ1 τ2 : Tp} {e0 : [] |- (τ1 ->s τ2)} {e0' : (τ1 :: []) |- τ2} {e1 v1 : [] |- τ1} {v : [] |- τ2}
               → evals e0 (lam e0') n0
               → evals e1 v1 n1
               → evals (subst (lem3 v1) e0') v n
               → evals (app e0 e1) v ((n0 +c n1) +c n)
      z-evals : evals z z 0c
      s-evals : ∀ {n}
              → {e v : [] |- nat}
              → evals e v n
              → evals (suc e) (suc v) n 
      unit-evals : evals unit unit 0c
      rec-evals : ∀ {n1 n2}
                  → {τ : Tp} {e v : [] |- nat} {e0 v' : [] |- τ} {e1 : (nat :: (susp τ :: [])) |- τ}
                  → evals e v n1
                  → evals-rec-branch e0 e1 v v' n2
                  → evals (rec e e0 e1) v' (n1 +c (1c +c n2))
      -- adding some new rules to the mix
      delay-evals : {τ : Tp} {e : [] |- τ}
                  → evals (delay e) (delay e) 0c
      force-evals : ∀ {n1 n2}
                  → {τ : Tp} {e' v : [] |- τ} {e : [] |- susp τ}
                  → evals e (delay e') n1
                  → evals e' v n2
                  → evals (force e) v (n1 +c n2)
      split-evals : ∀ {n1 n2}
                  → {τ τ1 τ2 : Tp} {e0 : [] |- (τ1 ×s τ2)} {v1 : [] |- τ1} {v2 : [] |- τ2} {e1 : (τ1 :: (τ2 :: [])) |- τ} {v : [] |- τ}
                  → evals e0 (prod v1 v2) n1
                  → evals (subst (lem4 v1 v2) e1) v n2
                  → evals (split e0 e1) v (n1 +c n2)

    -- means   evals (rec v e0 e1) v' n 
    -- but helpful to have a separate type for this
    data evals-rec-branch {τ : Tp} (e0 : [] |- τ) (e1 : (nat :: (susp τ :: [])) |- τ) : (e : [] |- nat) (v : [] |- τ) → Cost → Set where
         evals-rec-z : ∀ {v n} → evals e0 v n → evals-rec-branch e0 e1 z v n 
         evals-rec-s : ∀ {v v' n} → evals (subst (lem4 v (delay (rec v e0 e1))) e1) v' n
                               → evals-rec-branch e0 e1 (suc v) v' n 

  evals-val : {τ : Tp} {e : [] |- τ} {v : [] |- τ} {n : Cost} → evals e v n → val v
  evals-val (pair-evals D D₁) = pair-isval _ _ (evals-val D) (evals-val D₁)
  evals-val lam-evals = lam-isval _
  evals-val (app-evals D D₁ D₂) = evals-val D₂
  evals-val z-evals = z-isval
  evals-val (s-evals D) = suc-isval _ (evals-val D)
  evals-val unit-evals = unit-isval
  evals-val (rec-evals x (evals-rec-z D)) = evals-val D
  evals-val (rec-evals x (evals-rec-s D)) = evals-val D 
  evals-val delay-evals = delay-isval _
  evals-val (force-evals D D₁) = evals-val D₁
  evals-val (split-evals D D₁) = evals-val D₁

  val-evals-inversion : {τ : Tp} {v v' : [] |- τ} {n : Cost} → val v → evals v v' n → (v == v') × Equals0c n
  val-evals-inversion z-isval z-evals = Refl , Eq0-0c
  val-evals-inversion (suc-isval e valv) (s-evals evv) = ap suc (fst IH) , snd IH where
    IH = val-evals-inversion valv evv
  val-evals-inversion (pair-isval e1 e2 valv valv₁) (pair-evals evv evv₁) = ap2 prod (fst IH1) (fst IH2) , Eq0-+c (snd IH1) (snd IH2) where
    IH1 = val-evals-inversion valv evv
    IH2 = val-evals-inversion valv₁ evv₁
  val-evals-inversion (lam-isval e) lam-evals = Refl , Eq0-0c
  val-evals-inversion unit-isval unit-evals = Refl , Eq0-0c
  val-evals-inversion (delay-isval e) delay-evals = Refl , Eq0-0c

---------- some sample programs in the source language

  --dbl(n : nat) = 2*n
  dbl : ∀ {Γ} → Γ |- (nat ->s nat)
  dbl = lam (rec (var i0) z (suc (suc (force (var (iS i0))))))
 
  --add(x : nat , y : nat) = x+y
  add : ∀ {Γ} → Γ |- (nat ->s (nat ->s nat))
  add = lam (lam (rec (var (iS i0)) (var i0) (suc (force (var (iS i0))))))

  --mult(x : nat , y : nat) = x*y
  mult : ∀ {Γ} → Γ |- (nat ->s (nat ->s nat))
  mult = lam (lam (rec (var (iS i0)) z (app (app add (var (iS (iS i0)))) (force (var (iS i0))))))

{- Name: Bowornmet (Ben) Hudson

--Type safety and meaning functions for L{⇒,+,×,unit}--

-}

open import Preliminaries
open import Preorder
open import Preorder-repackage

module L where

  -- => and + and × and unit
  data Typ : Set where
    _⇒_ : Typ → Typ → Typ
    _×'_ : Typ → Typ → Typ
    _+'_ : Typ → Typ → Typ
    unit : Typ

------------------------------------------

  -- represent a context as a list of types
  Ctx = List Typ

  -- de Bruijn indices (for free variables)
  data _∈_ : Typ → Ctx → Set where
    i0 : ∀ {Γ τ}
       → τ ∈ (τ :: Γ)
    iS : ∀ {Γ τ τ1}
       → τ ∈ Γ
       → τ ∈ (τ1 :: Γ)

------------------------------------------

  -- static semantics
  data _|-_ : Ctx → Typ → Set where
    var : ∀ {Γ τ}
        → (x : τ ∈ Γ) → Γ |- τ
    lam : ∀ {Γ τ ρ}
        → (x : (ρ :: Γ) |- τ)
        → Γ |- (ρ ⇒ τ)
    app : ∀ {Γ τ1 τ2}
       → (e1 : Γ |- (τ2 ⇒ τ1)) → (e2 : Γ |- τ2)
       → Γ |- τ1
    unit : ∀ {Γ}
         → Γ |- unit
    prod : ∀ {Γ τ1 τ2}
         → (e1 : Γ |- τ1) → (e2 : Γ |- τ2)
         → Γ |- (τ1 ×' τ2)
    l-proj : ∀ {Γ τ1 τ2}
           → (e : Γ |- (τ1 ×' τ2))
           → Γ |- τ1
    r-proj : ∀ {Γ τ1 τ2}
           → (e : Γ |- (τ1 ×' τ2))
           → Γ |- τ2
    inl : ∀ {Γ τ1 τ2}
        → (e : Γ |- τ1)
        → Γ |- (τ1 +' τ2)
    inr : ∀ {Γ τ1 τ2}
        → (e : Γ |- τ2)
        → Γ |- (τ1 +' τ2)
    case` : ∀ {Γ τ1 τ2 τ}
         → (e : Γ |- (τ1 +' τ2))
         → (e1 : (τ1 :: Γ) |- τ)
         → (e2 : (τ2 :: Γ) |- τ)
         → Γ |- τ

------------------------------------------

  -- renaming
  rctx : Ctx → Ctx → Set
  rctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → τ ∈ Γ

  -- re: transferring variables in contexts
  lem1 : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) (τ :: Γ')
  lem1 d i0 = i0
  lem1 d (iS x) = iS (d x)

  -- renaming lemma
  ren : ∀ {Γ Γ' τ} → Γ' |- τ → rctx Γ Γ' → Γ |- τ
  ren (var x) d = var (d x)
  ren (lam e) d = lam (ren e (lem1 d))
  ren (app e1 e2) d = app (ren e1 d) (ren e2 d)
  ren unit d = unit
  ren (prod e1 e2) d = prod (ren e1 d) (ren e2 d)
  ren (l-proj e) d = l-proj (ren e d)
  ren (r-proj e) d = r-proj (ren e d)
  ren (inl x) d = inl (ren x d)
  ren (inr x) d = inr (ren x d)
  ren (case` e e1 e2) d = case` (ren e d) (ren e1 (lem1 d)) (ren e2 (lem1 d))

------------------------------------------

  -- substitution
  sctx : Ctx → Ctx → Set
  sctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → Γ |- τ

  -- weakening (didn't need this later on. Oh well)
  wkn : ∀ {Γ τ1 τ2} → Γ |- τ2 → (τ1 :: Γ) |- τ2
  wkn e = ren e iS

  -- lem2 (need a lemma for subst like we did for renaming)
  lem2 : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) (τ :: Γ')
  lem2 d i0 = var i0
  lem2 d (iS i0) = ren (d i0) iS
  lem2 d (iS (iS i)) = ren (d (iS i)) iS

  -- another substitution lemma
  lem3 : ∀ {Γ τ} → Γ |- τ → sctx Γ (τ :: Γ)
  lem3 d i0 = d
  lem3 d (iS i) = var i

  -- one final lemma needed for the last stepping rule. Thank you Professor Licata!
  lem4 : ∀ {Γ τ1 τ2} → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ))
  lem4 x y i0 = x
  lem4 x y (iS i0) = y
  lem4 x y (iS (iS i)) = var i

  -- the 'real' substitution lemma
  subst : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ' |- τ → Γ |- τ
  subst d (var x) = d x
  subst d (lam e) = lam (subst (lem2 d) e)
  subst d (app e1 e2) = app (subst d e1) (subst d e2)
  subst d unit = unit
  subst d (prod e1 e2) = prod (subst d e1) (subst d e2)
  subst d (l-proj e) = l-proj (subst d e)
  subst d (r-proj e) = r-proj (subst d e)
  subst d (inl x) = inl (subst d x)
  subst d (inr x) = inr (subst d x)
  subst d (case` e e1 e2) = case` (subst d e) (subst (lem2 d) e1) (subst (lem2 d) e2)

------------------------------------------

  -- closed values of L (when something is a value)
  -- recall that we use empty contexts when we work with dynamic semantics
  data val : ∀ {τ} → [] |- τ → Set where
    unit-isval : val unit
    lam-isval : ∀ {ρ τ} (e : (ρ :: []) |- τ)
              → val (lam e)
    prod-isval : ∀ {τ1 τ2}
               → (e1 : [] |- τ1) → (e2 : [] |- τ2)
               → val e1 → val e2
               → val (prod e1 e2)
    inl-isval : ∀ {τ1 τ2}
              → (e : [] |- τ1)
              → val e
              → val (inl {_} {_} {τ2} e)
    inr-isval : ∀ {τ1 τ2}
              → (e : [] |- τ2)
              → val e
              → val (inr {_} {τ1} {_} e)

------------------------------------------

  -- stepping rules (preservation is folded into this)
  -- Preservation: if e:τ and e=>e', then e':τ
  data _>>_ : ∀ {τ} → [] |- τ → [] |- τ → Set where
     app-steps : ∀ {τ1 τ2}
              → (e1 e1' : [] |- (τ2 ⇒ τ1)) → (e2 : [] |- τ2)
              → e1 >> e1'
              → (app e1 e2) >> (app e1' e2)
     app-steps-2 : ∀ {τ1 τ2}
                → (e1 : [] |- (τ2 ⇒ τ1)) → (e2 e2' : [] |- τ2)
                → val e1 → e2 >> e2'
                → (app e1 e2) >> (app e1 e2')
     app-steps-3 : ∀ {τ1 τ2}
                → (e1 : (τ1 :: []) |- τ2)
                → (e2 : [] |- τ1)
                → (app (lam e1) e2) >> subst (lem3 e2) e1
     prod-steps : ∀ {τ1 τ2}
                → (e1 e1' : [] |- τ1) → (e2 : [] |- τ2)
                → e1 >> e1'
                → (prod e1 e2) >> (prod e1' e2)
     prod-steps-2 : ∀ {τ1 τ2}
                  → (e1 : [] |- τ1) → (e2 e2' : [] |- τ2)
                  → val e1 → e2 >> e2'
                  → (prod e1 e2) >> (prod e1 e2')
     l-proj-steps : ∀ {τ1 τ2}
                  → (e e' : [] |- (τ1 ×' τ2))
                  → e >> e'
                  → (l-proj e) >> (l-proj e')
     l-proj-steps-2 : ∀ {τ1 τ2}
                    → (e1 : [] |- τ1) → (e2 : [] |- τ2)
                    → val e1 → val e2
                    → (l-proj (prod e1 e2)) >> e1
     r-proj-steps : ∀ {τ1 τ2}
                  → (e e' : [] |- (τ1 ×' τ2))
                  → e >> e'
                  → (r-proj e) >> (r-proj e')
     r-proj-steps-2 : ∀ {τ1 τ2}
                    → (e1 : [] |- τ1) → (e2 : [] |- τ2)
                    → val e1 → val e2
                    → (r-proj (prod e1 e2)) >> e2
     inl-steps : ∀ {τ1 τ2}
               → (e e' : [] |- τ1)
               → e >> e'
               → inl {_} {_} {τ2} e >> inl e'
     inr-steps : ∀ {τ1 τ2}
               → (e e' : [] |- τ2)
               → e >> e'
               → inr {_} {τ1} {_} e >> inr e'
     case`-steps : ∀ {τ1 τ2 τ}
                 → (e e' : [] |- (τ1 +' τ2))
                 → (e1 : (τ1 :: []) |- τ)
                 → (e2 : (τ2 :: []) |- τ)
                 → e >> e'
                 → (case` e e1 e2) >> (case` e' e1 e2)
     case`-steps-2 : ∀ {τ1 τ2 τ}
                   → (e : [] |- τ1)
                   → (e1 : (τ1 :: []) |- τ)
                   → (e2 : (τ2 :: []) |- τ)
                   → val e
                   → (case` (inl e) e1 e2) >> subst (lem3 e) e1
     case`-steps-3 : ∀ {τ1 τ2 τ}
                   → (e : [] |- τ2)
                   → (e1 : (τ1 :: []) |- τ)
                   → (e2 : (τ2 :: []) |- τ)
                   → val e
                   → (case` (inr e) e1 e2) >> subst (lem3 e) e2

------------------------------------------

  -- Proof of progress!
  -- Progress: if e:τ, then either e val or ∃e' such that e=>e'
  progress : ∀ {τ} (e : [] |- τ) → Either (val e) (Σ (λ e' → (e >> e')))
  progress (var ())
  progress (lam x) = Inl (lam-isval x)
  progress (app e1 e2) with progress e1 
  progress (app .(lam e) e2) | Inl (lam-isval e) = Inr (_ , app-steps-3 e e2)
  progress (app e1 e2) | Inr (x , d) = Inr (_ , app-steps e1 x e2 d)
  progress unit = Inl unit-isval
  progress (prod e1 e2) with progress e1
  progress (prod e1 e2) | Inl d with progress e2
  progress (prod e1 e2) | Inl d | Inl x = Inl (prod-isval e1 e2 d x)
  progress (prod e1 e2) | Inl d | Inr (x , k) = Inr (_ , prod-steps-2 e1 e2 x d k)
  progress (prod e1 e2) | Inr (x , d) = Inr (_ , prod-steps e1 x e2 d)
  progress (l-proj e) with progress e
  progress (l-proj .(prod e1 e2)) | Inl (prod-isval e1 e2 d d₁) = Inr (_ , l-proj-steps-2 e1 e2 d d₁)
  progress (l-proj e) | Inr (x , d) = Inr (_ , l-proj-steps e x d)
  progress (r-proj e) with progress e
  progress (r-proj .(prod e1 e2)) | Inl (prod-isval e1 e2 d d₁) = Inr (_ , r-proj-steps-2 e1 e2 d d₁)
  progress (r-proj e) | Inr (x , d) = Inr (_ , r-proj-steps e x d)
  progress (inl e) with progress e
  progress (inl e) | Inl x = Inl (inl-isval e x)
  progress (inl e) | Inr (x , d) = Inr (_ , inl-steps e x d)
  progress (inr e) with progress e
  progress (inr e) | Inl x = Inl (inr-isval e x)
  progress (inr e) | Inr (x , d) = Inr (_ , inr-steps e x d)
  progress (case` e e1 e2) with progress e
  progress (case` .(inl e) e1 e2) | Inl (inl-isval e x) = Inr (_ , case`-steps-2 e e1 e2 x)
  progress (case` .(inr e) e1 e2) | Inl (inr-isval e x) = Inr (_ , case`-steps-3 e e1 e2 x)
  progress (case` e e1 e2) | Inr (x , d) = Inr (_ , case`-steps e x e1 e2 d)

------------------------------------------

  -- how to interpret types in L as preorders

  interp : Typ → PREORDER
  interp (A ⇒ B) = interp A ->p interp B
  interp (A ×' B) = interp A ×p interp B
  interp (A +' B) = interp A +p interp B
  interp unit = unit-p

  interpC : Ctx → PREORDER
  interpC [] = unit-p
  interpC (A :: Γ) = interpC Γ ×p interp A

  -- look up a variable in context
  lookup : ∀{Γ τ} → τ ∈ Γ → el (interpC Γ ->p interp τ)
  lookup (i0 {Γ} {τ}) = snd' {interpC (τ :: Γ)} {interpC Γ} {_} id
  lookup (iS {Γ} {τ} {τ1} x) = comp {interpC (τ1 :: Γ)} {_} {_} (fst' {interpC (τ1 :: Γ)} {_} {interp τ1} id) (lookup x)

  interpE : ∀{Γ τ} → Γ |- τ → el (interpC Γ ->p interp τ)
  interpE (var x) = lookup x
  interpE (lam e) = lam' (interpE e)
  interpE (app e1 e2) = app' (interpE e1) (interpE e2)
  interpE unit = monotone (λ _ → <>) (λ x y _ → <>)
  interpE (prod e1 e2) = pair' (interpE e1) (interpE e2)
  interpE (l-proj {Γ} {τ1} {τ2} e) = fst' {_} {_} {interp τ2} (interpE e)
  interpE (r-proj {Γ} {τ1} {τ2} e) = snd' {_} {interp τ1} {_} (interpE e)
  interpE (inl e) = inl' (interpE e)
  interpE (inr e) = inr' (interpE e)
  interpE (case` e e1 e2) = case' (interpE e1) (interpE e2) (interpE e)

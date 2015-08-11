{- Name: Bowornmet (Ben) Hudson

--Complexity : "Playing The Game"--

-}

open import Preliminaries
open import Preorder-withmax

module Complexity-lang where

  data Typ : Set where
    nat : Typ
    _×'_ : Typ → Typ → Typ
    _⇒_ : Typ → Typ → Typ
    unit : Typ

------------------------------------------

  -- represent a context as a list of types
  Ctx = List Typ

  -- de Bruijn indices (for free variables)
  data _∈_ : Typ → Ctx → Set where
    i0 : ∀ {Γ T}
       → T ∈ (T :: Γ)
    iS : ∀ {Γ T T1}
       → T ∈ Γ
       → T ∈ (T1 :: Γ)

------------------------------------------

  -- some syntax
  data _|-_ : Ctx → Typ → Set where
    var : ∀ {Γ T}
        → (x : T ∈ Γ) → Γ |- T
    z : ∀ {Γ}
      → Γ |- nat
    suc : ∀ {Γ}
        → (e : Γ |- nat)
        → Γ |- nat
    rec : ∀ {Γ T}
        → (e : Γ |- nat)
        → (e0 : Γ |- T)
        → (e1 : (nat :: (T :: Γ)) |- T)
        → Γ |- T
    lam : ∀ {Γ T Ρ}
        → (x : (Ρ :: Γ) |- T)
        → Γ |- (Ρ ⇒ T)
    app : ∀ {Γ T1 T2}
        → (e1 : Γ |- (T2 ⇒ T1)) → (e2 : Γ |- T2)
        → Γ |- T1
    unit : ∀ {Γ}
         → Γ |- unit
    prod : ∀ {Γ T1 T2}
         → (e1 : Γ |- T1) → (e2 : Γ |- T2)
         → Γ |- (T1 ×' T2)
    l-proj : ∀ {Γ T1 T2}
           → (e : Γ |- (T1 ×' T2))
           → Γ |- T1
    r-proj : ∀ {Γ T1 T2}
           → (e : Γ |- (T1 ×' T2))
           → Γ |- T2

------------------------------------------

  -- renaming function
  rctx : Ctx → Ctx → Set
  rctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → τ ∈ Γ

  lem1 : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) (τ :: Γ')
  lem1 d i0 = i0
  lem1 d (iS x) = iS (d x)

  ren : ∀ {Γ Γ' τ} → Γ' |- τ → rctx Γ Γ' → Γ |- τ
  ren (var x) d = var (d x)
  ren z d = z
  ren (suc e) d = suc (ren e d)
  ren (rec e0 e1 e2) d = rec (ren e0 d) (ren e1 d) (ren e2 (lem1 (lem1 d)))
  ren (lam x) d = lam (ren x (lem1 d))
  ren (app e1 e2) d = app (ren e1 d) (ren e2 d)
  ren unit d = unit
  ren (prod e1 e2) d = prod (ren e1 d) (ren e2 d)
  ren (l-proj e) d = l-proj (ren e d)
  ren (r-proj e) d = r-proj (ren e d)

------------------------------------------

  -- substitution
  sctx : Ctx → Ctx → Set
  sctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → Γ |- τ

  -- weakening
  wkn : ∀ {Γ τ1 τ2} → Γ |- τ2 → (τ1 :: Γ) |- τ2
  wkn e = ren e iS

  -- lemmas everywhere
  wkn-s : ∀ {Γ τ1 Γ'} → sctx Γ Γ' → sctx (τ1 :: Γ) Γ'
  wkn-s d = λ f → wkn (d f)

  wkn-r : ∀ {Γ τ1 Γ'} → rctx Γ Γ' → rctx (τ1 :: Γ) Γ'
  wkn-r d = λ x → iS (d x)

  lem2 : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) (τ :: Γ')
  lem2 d i0 = var i0
  lem2 d (iS i) = wkn (d i)

  lem3 : ∀ {Γ τ} → Γ |- τ → sctx Γ (τ :: Γ)
  lem3 e i0 = e
  lem3 e (iS i) = var i

  lem4 : ∀ {Γ τ1 τ2} → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ))
  lem4 e1 e2 i0 = e1
  lem4 e1 e2 (iS i0) = e2
  lem4 e1 e2 (iS (iS i)) = var i

  subst : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ' |- τ → Γ |- τ
  subst d (var x) = d x
  subst d z = z
  subst d (suc e) = suc (subst d e)
  subst d (rec e0 e1 e2) = rec (subst d e0) (subst d e1) (subst (lem2 (lem2 d)) e2)
  subst d (lam e) = lam (subst (lem2 d) e)
  subst d (app e1 e2) = app (subst d e1) (subst d e2)
  subst d unit = unit
  subst d (prod e1 e2) = prod (subst d e1) (subst d e2)
  subst d (l-proj e) = l-proj (subst d e)
  subst d (r-proj e) = r-proj (subst d e)

------------------------------------------

  -- define 'stepping' as a datatype (fig. 1 of proof)
  data _≤s_ : ∀ {Γ T} → Γ |- T → Γ |- T → Set where
    refl-s : ∀ {Γ T}
           → (e : Γ |- T)
           → e ≤s e
    trans-s : ∀ {Γ T}
            → (e e' e'' : Γ |- T)
            → e ≤s e' → e' ≤s e''
            → e ≤s e''
    cong-s : ∀ {Γ T T'}
           →  (e : (T :: Γ) |- T')
           → (e1 e2 : Γ |- T)
           → e1 ≤s e2
           → subst (lem3 e1) e ≤s subst (lem3 e2) e
    lam-s : ∀ {Γ T T'}
          → (e : (T :: Γ) |- T')
          → (e2 : Γ |- T)
          → subst (lem3 e2) e ≤s app (lam e) e2
    l-proj-s : ∀ {Γ T1 T2}
             → (e1 : Γ |- T1) → (e2 : Γ |- T2)
             → e1 ≤s (l-proj (prod e1 e2))
    r-proj-s : ∀ {Γ T1 T2}
             → (e1 : Γ |- T1) → (e2 : Γ |- T2)
             → e2 ≤s (r-proj (prod e1 e2))
    rec-steps-s : ∀ {Γ T}
                → (e : Γ |- nat)
                → (e0 : Γ |- T)
                → (e1 : (nat :: (T :: Γ)) |- T)
                → subst (lem4 e (rec e e0 e1)) e1 ≤s (rec (suc e) e0 e1)
    rec-steps-z : ∀ {Γ T}
                → (e0 : Γ |- T)
                → (e1 : (nat :: (T :: Γ)) |- T)
                → e0 ≤s (rec z e0 e1)

------------------------------------------

  el : PREORDER → Set
  el = fst

  PREORDER≤ : (PA : PREORDER) → el PA → el PA → Set
  PREORDER≤ PA = Preorder-max-str.≤ (snd PA)

  interp : Typ → PREORDER
  interp nat = Nat , nat-p
  interp (A ×' B) = interp A ×p interp B
  interp (A ⇒ B) = interp A ->p interp B
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
  interpE z = monotone (λ x → Z) (λ x y _ → <>)
  interpE (suc e) = {!!} --monotone (λ x → S {!!}) {!!}
  interpE (rec e0 e1 e2) = mnatrec {!!} (interpE e1) (λ x x₁ → {!!}) {!!} --mnatrec {!!} (λ x x₁ → interpE e1) {!!}
  interpE (lam e) = lam' (interpE e)
  interpE (app e1 e2) = app' (interpE e1) (interpE e2)
  interpE unit = monotone (λ _ → <>) (λ x y _ → <>)
  interpE (prod e1 e2) = pair' (interpE e1) (interpE e2)
  interpE (l-proj {Γ} {τ1} {τ2} e) = fst' {_} {_} {interp τ2} (interpE e)
  interpE (r-proj {Γ} {τ1} {τ2} e) = snd' {_} {interp τ1} {_} (interpE e)

  sound : ∀ {Γ τ} (e e' : Γ |- τ) → e ≤s e' → PREORDER≤ (interpC Γ ->p interp τ) (interpE e) (interpE e')
  sound {_} {τ} .e' e' (refl-s .e') k = Preorder-max-str.refl (snd (interp τ)) (Monotone.f (interpE e') k)
  sound {_} {τ} e e' (trans-s .e e'' .e' p p₁) k = Preorder-max-str.trans (snd (interp τ)) (Monotone.f (interpE e) k)
                                                     (Monotone.f (interpE e'') k) (Monotone.f (interpE e') k)
                                                     (sound e e'' p k) (sound e'' e' p₁ k)
  sound .(subst (lem3 e1) e) .(subst (lem3 e2) e) (cong-s e e1 e2 p) k = {!!}
  sound .(subst (lem3 e2) e) .(app (lam e) e2) (lam-s e e2) k = {!!}
  sound {_} {τ} e .(l-proj (prod e e2)) (l-proj-s .e e2) k = Preorder-max-str.refl (snd (interp τ)) (Monotone.f (interpE e) k)
  sound {_} {τ} e .(r-proj (prod e1 e)) (r-proj-s e1 .e) k = Preorder-max-str.refl (snd (interp τ)) (Monotone.f (interpE e) k)
  sound .(subst (lem4 e (rec e e0 e1)) e1) .(rec (suc e) e0 e1) (rec-steps-s e e0 e1) k = {!!}
  sound e .(rec z e e1) (rec-steps-z .e e1) k = {!!}

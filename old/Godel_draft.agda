{- Name: Bowornmet (Ben) Hudson

--Progress and Preservation in Godel's T--

Progress: if e:τ, then either e val or ∃e' such that e=>e'.
Preservation: if e:τ and e=>e', then e':τ.

-}

module Godel_draft where

  -- nat and =>
  data Typ : Set where
    nat : Typ
    _⇒_ : Typ → Typ → Typ

  -- lists
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  -- existential quantifier
  data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (a : A) → B a → Σ A B

  syntax Σ A (\ x  -> B) = Σ[ x ∈ A ] B

  -- ('a,'b) choice
  data Either (A B : Set) : Set where
    Inl : A → Either A B
    Inr : B → Either A B

  -- representing a context as a list of types
  Ctx = List Typ

  -- de Bruijn indices
  data _∈_ : Typ → Ctx → Set where
    i0 : ∀ {Γ τ}
       → τ ∈ (τ :: Γ)
    iS : ∀ {Γ τ τ1}
       → τ ∈ Γ
       → τ ∈ (τ1 :: Γ)

  -- static semantics
  data _|-_ : Ctx → Typ → Set where
    var : ∀ {Γ τ}
        → (x : τ ∈ Γ) → Γ |- τ
    z : ∀ {Γ}
      → Γ |- nat
    suc : ∀ {Γ}
        → (e : Γ |- nat)
        → Γ |- nat
    rec : ∀ {Γ τ}
        → (e : Γ |- nat)
        → (e0 : Γ |- τ)
        → (e1 : (nat :: (τ :: Γ)) |- τ)
        → Γ |- τ
    lam : ∀ {Γ τ ρ}
        → (x : (ρ :: Γ) |- τ)
        → Γ |- (ρ ⇒ τ)
    ap : ∀ {Γ τ1 τ2}
       → (e1 : Γ |- (τ2 ⇒ τ1)) → (e2 : Γ |- τ2)
       → Γ |- τ1

-------------------------

  -- renaming
  rctx : Ctx → Ctx → Set
  rctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → τ ∈ Γ

  -- re: transferring variables in contexts (I don't know how to formally name this lemma...)
  lem1 : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) (τ :: Γ')
  lem1 d i0 = i0
  lem1 d (iS x) = iS (d x)

  -- renaming lemma
  ren : ∀ {Γ Γ' τ} → Γ' |- τ → rctx Γ Γ' → Γ |- τ
  ren (var x) d = var (d x)
  ren z d = z
  ren (suc e) d = suc (ren e d)
  ren (rec e e0 e1) d = rec (ren e d) (ren e0 d) (ren e1 (lem1 (lem1 d)))
  ren (lam e) d = lam (ren e (lem1 d))
  ren (ap e1 e2) d = ap (ren e1 d) (ren e2 d)

------------------------------------------

  -- substitution
  sctx : Ctx → Ctx → Set
  sctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → Γ |- τ

  -- weakening
  wkn : ∀ {Γ τ1 τ2} → Γ |- τ2 → (τ1 :: Γ) |- τ2
  wkn e = ren e iS

  -- lem2 (need a lemma for subst like we did for renaming)
  lem2 : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) (τ :: Γ')
  lem2 d i0 = var i0
  lem2 d (iS x) = ren (d x) iS

  -- substitution lemma
  subs : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ' |- τ → Γ |- τ
  subs d (var x) = d x
  subs d z = z
  subs d (suc e) = suc (subs d e)
  subs d (rec e e0 e1) = rec (subs d e) (subs d e0) (subs (lem2 (lem2 d)) e1)
  subs d (lam e) = lam (subs (lem2 d) e)
  subs d (ap e1 e2) = ap (subs d e1) (subs d e2)

------------------------------------------

  -- lem3 for substitution.
  lem3 : ∀ {Γ τ} → Γ |- τ → sctx Γ (τ :: Γ)
  lem3 e i0 = e
  lem3 e (iS d) = var d

  -- the final lemma. Thank you Professor Licata!
  subst-lemma : ∀ {τ1 τ2} → [] |- τ1 → [] |- τ2 → sctx [] (τ1 :: (τ2 :: []))
  subst-lemma x y i0 = x
  subst-lemma x y (iS i0) = y
  subst-lemma x y (iS (iS i)) = var i

------------------------------------------

  -- closed values of L{nat,⇒} (when something is a value)
  data val : ∀ {τ} → [] |- τ → Set where
    z-isval : val z
    suc-isval : (e : [] |- nat) → (val e)
              → val (suc e)
    lam-isval : ∀ {ρ τ} (e : (ρ :: []) |- τ)
              →  val (lam e)

------------------------------------------

  -- stepping rules (preservation is folded into this)
  -- Preservation: if e:τ and e=>e', then e':τ
  data _>>_ : ∀ {τ} → [] |- τ → [] |- τ → Set where
     suc-steps : (e e' : [] |- nat)
               → e >> e'
               → (suc e) >> (suc e')
     ap-steps : ∀ {τ1 τ2}
              → (e1 e1' : [] |- (τ2 ⇒ τ1)) → (e2 : [] |- τ2)
              → e1 >> e1'
              → (ap e1 e2) >> (ap e1' e2)
     ap-steps-2 : ∀ {τ1 τ2}
                → (e1 : [] |- (τ2 ⇒ τ1)) → (e2 e2' : [] |- τ2)
                → val e1 → e2 >> e2'
                → (ap e1 e2) >> (ap e1 e2')
     ap-steps-3 : ∀ {τ1 τ2}
                → (e1 : (τ1 :: []) |- τ2)
                → (e2 : [] |- τ1)
                → (ap (lam e1) e2) >> subs (lem3 e2) e1
     rec-steps : ∀ {τ}
               → (e e' : [] |- nat)
               → (e0 : [] |- τ)
               → (e1 : (nat :: (τ :: [])) |- τ)
               → e >> e'
               → (rec e e0 e1) >> (rec e' e0 e1)
     rec-steps-z : ∀ {τ}
                 → (e : val z)
                 → (e0 : [] |- τ)
                 → (e1 : (nat :: (τ :: [])) |- τ)
                 → (rec z e0 e1) >> e0
     rec-steps-suc : ∀ {τ}
                   → (e : [] |- nat)
                   → (e0 : [] |- τ)
                   → (e1 : (nat :: (τ :: [])) |- τ)
                   → val e
                   → (rec (suc e) e0 e1) >> subs (subst-lemma e (rec e e0 e1)) e1

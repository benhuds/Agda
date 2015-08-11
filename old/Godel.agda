{- Name: Bowornmet (Ben) Hudson

--Progress and Preservation in Godel's T--

Progress: if e:τ, then either e val or ∃e' such that e=>e'.
Preservation: if e:τ and e=>e', then e':τ.

-}

open import Preliminaries

module Godel where

  -- nat and =>
  data Typ : Set where
    nat : Typ
    _⇒_ : Typ → Typ → Typ

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
    app : ∀ {Γ τ1 τ2}
       → (e1 : Γ |- (τ2 ⇒ τ1)) → (e2 : Γ |- τ2)
       → Γ |- τ1

------------------------------------------

  -- renaming function
  rctx : Ctx → Ctx → Set
  rctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → τ ∈ Γ

  -- re: transferring variables in contexts
  lem1 : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) (τ :: Γ')
  lem1 d i0 = i0
  lem1 d (iS x) = iS (d x)

  -- renaming lemma
  ren : ∀ {Γ Γ' τ} → Γ' |- τ → rctx Γ Γ' → Γ |- τ
  ren (var x) d = var (d x)
  ren z d = z
  ren (suc e) d = suc (ren e d)
  ren (rec e e0 e1) d = rec (ren e d) (ren e0 d) (ren e1 (lem1(lem1 d)))
  ren (lam e) d = lam (ren e (lem1 d))
  ren (app e1 e2) d = app (ren e1 d) (ren e2 d)

------------------------------------------

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

  -- one final lemma needed for the last stepping rule. Thank you Professor Licata!
  lem4 : ∀ {Γ τ1 τ2} → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ))
  lem4 e1 e2 i0 = e1
  lem4 e1 e2 (iS i0) = e2
  lem4 e1 e2 (iS (iS i)) = var i

  -- the 'real' substitution lemma (if (x : τ') :: Γ |- (e : τ) and Γ |- (e : τ') , then Γ |- e[x -> e'] : τ)
  subst : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ' |- τ → Γ |- τ
  subst d (var x) = d x
  subst d z = z
  subst d (suc e) = suc (subst d e)
  subst d (rec e e0 e1) = rec (subst d e) (subst d e0) (subst (lem2 (lem2 d)) e1)
  subst d (lam e) = lam (subst (lem2 d) e)
  subst d (app e1 e2) = app (subst d e1) (subst d e2)

------------------------------------------

  -- closed values of L{nat,⇒} (when something is a value)
  -- recall that we use empty contexts when we work with dynamic semantics
  data val : ∀ {τ} → [] |- τ → Set where
    z-isval : val z
    suc-isval : (e : [] |- nat) → (val e)
              → val (suc e)
    lam-isval : ∀ {ρ τ} (e : (ρ :: []) |- τ)
              → val (lam e)

------------------------------------------

  -- stepping rules (preservation is folded into this)
  -- Preservation: if e:τ and e=>e', then e':τ
  data _>>_ : ∀ {τ} → [] |- τ → [] |- τ → Set where
     suc-steps : (e e' : [] |- nat)
               → e >> e'
               → (suc e) >> (suc e')
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
                   → (rec (suc e) e0 e1) >> subst (lem4 e (rec e e0 e1)) e1

------------------------------------------

  -- Proof of progress!
  -- Progress: if e:τ, then either e val or ∃e' such that e=>e'
  progress : ∀ {τ} (e : [] |- τ) → Either (val e) (Σ (λ e' → (e >> e')))
  progress (var ())
  progress z = Inl z-isval
  progress (suc e) with progress e
  progress (suc e) | Inl d = Inl (suc-isval e d)
  progress (suc e) | Inr (e' , d) = Inr (suc e' , suc-steps e e' d)
  progress (rec e e1 e2) with progress e
  progress (rec .z e1 e2) | Inl z-isval = Inr (e1 , rec-steps-z z-isval e1 e2)
  progress (rec .(suc e) e1 e2) | Inl (suc-isval e d) = Inr (subst (lem4 e (rec e e1 e2)) e2 , rec-steps-suc e e1 e2 d)
  progress (rec e e1 e2) | Inr (e' , d) = Inr (rec e' e1 e2 , rec-steps e e' e1 e2 d)
  progress (lam e) = Inl (lam-isval e)
  progress (app e1 e2) with progress e1
  progress (app .(lam e) e2) | Inl (lam-isval e) = Inr (subst (lem3 e2) e , app-steps-3 e e2)
  progress (app e1 e2) | Inr (e1' , d) = Inr (app e1' e2 , app-steps e1 e1' e2 d)

------------------------------------------

  -- Denotational semantics

  -- interpreting a T type in Agda
  interp : Typ → Set
  interp nat = Nat
  interp (A ⇒ B) = interp A → interp B

  -- interpreting contexts
  interpC : Ctx → Set
  interpC [] = Unit
  interpC (A :: Γ) = interpC Γ × interp A

  -- helper function to look a variable up in an interpC gamma
  lookupC : ∀{Γ A} → (x : A ∈ Γ) → interpC Γ → interp A
  lookupC i0 (recur , return) = return
  lookupC (iS i) (recur , return) = lookupC i recur

  -- primitive recursion function corresponding to rec
  natrec : ∀{C : Set} → C → (Nat → C → C) → Nat → C
  natrec base step Z = base
  natrec base step (S n) = step n (natrec base step n)

  -- interpreting expressions in Godel's T as a function from the interpretation of the context to the interpretation of its corresponding type
  interpE : ∀{Γ τ} → Γ |- τ → (interpC Γ → interp τ)
  interpE (var x) d = lookupC x d
  interpE z d = Z
  interpE (suc e) d = S (interpE e d)
  interpE (rec e e0 e1) d = natrec (interpE e0 d)  (λ n k → interpE e1 ((d , k) , n)) (interpE e d)
  interpE (lam e) d = λ x → interpE e (d , x)
  interpE (app e1 e2) d = interpE e1 d (interpE e2 d)

  helper : ∀ {Γ Γ' τ} → sctx Γ (τ :: Γ') → sctx Γ Γ'
  helper d = λ x → d (iS x)

  helper-r : ∀ {Γ Γ' τ} → rctx Γ (τ :: Γ') → rctx Γ Γ'
  helper-r d = λ x → d (iS x)

  -- compositionality of functions
  interpS : ∀ {Γ Γ'} → sctx Γ Γ' → interpC Γ → interpC Γ'
  interpS {Γ} {[]} a b = <>
  interpS {Γ} {A :: Γ'} a b = interpS (helper a) b , interpE (a i0) b

  interpR : ∀ {Γ Γ'} → rctx Γ Γ' → interpC Γ → interpC Γ'
  interpR {Γ} {[]} a b = <>
  interpR {Γ} {A :: Γ'} a b = interpR (helper-r a) b , lookupC (a i0) b

  --lemmas for lambda case of interpR-lemma
  interpR-lemma-lemma-lemma : ∀ {Γ Γ' τ} → (x : interp τ) → (Θ : rctx Γ Γ') → (Θ' : interpC Γ) → (interpR Θ Θ') == interpR (wkn-r Θ) (Θ' , x)
  interpR-lemma-lemma-lemma {Γ} {[]} x Θ Θ' = Refl
  interpR-lemma-lemma-lemma {Γ} {A :: Γ'} x Θ Θ' = ap (λ h → h , lookupC (Θ i0) Θ') (interpR-lemma-lemma-lemma x (helper-r Θ) Θ')

  interpR-lemma-lemma : ∀ {Γ Γ' τ} → (x : interp τ) → (Θ : rctx Γ Γ') → (Θ' : interpC Γ) → (interpR Θ Θ' , x) == (interpR (lem1 Θ) (Θ' , x))
  interpR-lemma-lemma {Γ} {[]} x Θ Θ' = Refl
  interpR-lemma-lemma {Γ} {A :: Γ'} x Θ Θ' = ap (λ h → h , x) (interpR-lemma-lemma-lemma x Θ Θ')

  interpR-lemma-lemma-rec : ∀ {Γ Γ' τ} → (x : interp nat) → (y : interp τ) → (Θ : rctx Γ Γ') → (Θ' : interpC Γ)
                                         → ((interpR Θ Θ' , y) , x) == interpR (lem1 (lem1 Θ)) ((Θ' , y) , x)
  interpR-lemma-lemma-rec x y Θ Θ' = interpR-lemma-lemma x (lem1 Θ) (Θ' , y) ∘ ap (λ h → h , x) (interpR-lemma-lemma y Θ Θ')

  interpR-lemma : ∀ {Γ Γ' τ} (e : Γ' |- τ) → (Θ : rctx Γ Γ') → (Θ' : interpC Γ) → (interpE e) (interpR Θ Θ') == (interpE (ren e Θ)) Θ'
  interpR-lemma (var i0) Θ Θ' = Refl
  interpR-lemma (var (iS x)) Θ Θ' = interpR-lemma (var x) (helper-r Θ) Θ'
  interpR-lemma z Θ Θ' = Refl
  interpR-lemma (suc e) Θ Θ' = ap S (interpR-lemma e Θ Θ')
  interpR-lemma {Γ} {Γ'} {τ} (rec e e1 e2) Θ Θ' = natrec (interpE e1 (interpR Θ Θ'))
                                                    (λ n k → interpE e2 ((interpR Θ Θ' , k) , n))
                                                      (interpE e (interpR Θ Θ'))                       =⟨ ap
                                                                                                          (λ h →
                                                                                                            natrec h (λ n k → interpE e2 ((interpR Θ Θ' , k) , n))
                                                                                                              (interpE e (interpR Θ Θ')))
                                                                                                                (interpR-lemma e1 Θ Θ') ⟩
                                                  natrec (interpE (ren e1 Θ) Θ')
                                                    (λ n k → interpE e2 ((interpR Θ Θ' , k) , n))
                                                      (interpE e (interpR Θ Θ'))                       =⟨ ap
                                                                                                          (λ h →
                                                                                                            natrec (interpE (ren e1 Θ) Θ')
                                                                                                              (λ n k → interpE e2 ((interpR Θ Θ' , k) , n)) h)
                                                                                                                (interpR-lemma e Θ Θ') ⟩
                                                  natrec (interpE (ren e1 Θ) Θ')
                                                    (λ n k → interpE e2 ((interpR Θ Θ' , k) , n))
                                                      (interpE (ren e Θ) Θ')                           =⟨ ap
                                                                                                          (λ h → 
                                                                                                            natrec (interpE (ren e1 Θ) Θ') h (interpE (ren e Θ) Θ'))
                                                                                                          (λ=
                                                                                                            (λ x →
                                                                                                          λ=
                                                                                                            (λ y →
                                                                                                              ap (λ h → interpE e2 h) (interpR-lemma-lemma-rec x y Θ Θ')))) ⟩
                                                  natrec (interpE (ren e1 Θ) Θ')
                                                    (λ n k → interpE e2 (interpR (lem1 (lem1 Θ)) ((Θ' , k) , n)))
                                                      (interpE (ren e Θ) Θ')                           =⟨ ap 
                                                                                                          (λ h → 
                                                                                                            natrec (interpE (ren e1 Θ) Θ') h (interpE (ren e Θ) Θ'))
                                                                                                          (λ=
                                                                                                            (λ x →
                                                                                                          λ=
                                                                                                            (λ y →
                                                                                                              interpR-lemma {nat :: τ :: Γ} {nat :: τ :: Γ'} e2 (lem1 (lem1 Θ))
                                                                                                                ((Θ' , y) , x)))) ⟩
                                                  natrec (interpE (ren e1 Θ) Θ')
                                                    (λ n k → interpE (ren e2 (lem1 (lem1 Θ))) ((Θ' , k) , n))
                                                       (interpE (ren e Θ) Θ')                          ∎

  interpR-lemma {Γ} {Γ'} {ρ ⇒ τ} (lam e) Θ Θ' = interpE (lam e) (interpR Θ Θ') =⟨ Refl ⟩
                              (λ x → interpE e (interpR Θ Θ' , x)) =⟨ λ= (λ x → ap (λ h → interpE e h) (interpR-lemma-lemma x Θ Θ')) ⟩
                              (λ x → interpE e (interpR (lem1 Θ) (Θ' , x))) =⟨ λ= (λ x → interpR-lemma {ρ :: Γ} {ρ :: Γ'} e (lem1 Θ) (Θ' , x)) ⟩
                              ((λ x → interpE (ren e (lem1 Θ)) (Θ' , x)) ∎)
                               
  interpR-lemma (app e1 e2) Θ Θ' = interpE (app e1 e2) (interpR Θ Θ')                     =⟨ Refl ⟩
                                   interpE e1 (interpR Θ Θ') (interpE e2 (interpR Θ Θ'))  =⟨ ap (λ x → x (interpE e2 (interpR Θ Θ'))) (interpR-lemma e1 Θ Θ') ⟩
                                   interpE (ren e1 Θ) Θ' (interpE e2 (interpR Θ Θ'))      =⟨ ap (λ x → interpE (ren e1 Θ) Θ' x) (interpR-lemma e2 Θ Θ')  ⟩
                                   interpE (ren e1 Θ) Θ' (interpE (ren e2 Θ) Θ')          ∎

  -- no proof is possible without the genius of Dan Licata
  mutual
    wkn-lemma : ∀ {Γ τ} (a : interp τ) → (Θ' : interpC Γ) →  Θ' == interpR iS (Θ' , a)
    wkn-lemma a Θ' = interpR-lemma-lemma-lemma a (λ x → x) Θ' ∘ ! (mutual-lemma Θ')

    mutual-lemma : ∀ {Γ} (Θ' : interpC Γ) → interpR (λ x → x) Θ' == Θ'
    mutual-lemma {[]} Θ' = Refl
    mutual-lemma {A :: Γ} (Θ' , a) = ! (ap (λ h → h , a) (wkn-lemma a Θ'))

  interp-lemma2 : ∀ {Γ τ' Θ' τ} (a : interp τ) → (e : Γ |- τ') → interpE e Θ' == interpE (wkn e) (Θ' , a)
  interp-lemma2 {Γ} {τ'} {Θ'} a e = interpE e Θ'                      =⟨ ap (λ x → interpE e x) (wkn-lemma a Θ') ⟩
                                    interpE e (interpR iS (Θ' , a))   =⟨ interpR-lemma e iS (Θ' , a) ⟩
                                    interpE (ren e iS) (Θ' , a)       ∎

  interp-lemma : ∀ {Γ Γ' Θ' τ} (a : interp τ) → (Θ : sctx Γ Γ') → interpS Θ Θ' == interpS (wkn-s Θ) (Θ' , a)
  interp-lemma {Γ} {[]} a Θ = Refl
  interp-lemma {Γ} {A :: Γ'} a Θ = ap2 (λ x y → x , y) (interp-lemma a (helper Θ)) (interp-lemma2 a (Θ i0))

  lemma : ∀ {Γ Γ' Θ' τ} (x : interp τ) → (Θ : sctx Γ Γ') → ((interpS Θ Θ') , x) == (interpS (lem2 Θ) (Θ' , x))
  lemma x Θ = ap (λ y → y , x) (interp-lemma x Θ)

  lemma-c-lemma-lemma : ∀ {Γ Γ' τ} → (x : interp τ) → (Θ : sctx Γ Γ') → (Θ' : interpC Γ) → (interpS Θ Θ') == (interpS (wkn-s Θ) (Θ' , x))
  lemma-c-lemma-lemma {Γ} {[]} x Θ Θ' = Refl
  lemma-c-lemma-lemma {Γ} {A :: Γ'} x Θ Θ' = ap2 (λ x₁ y → x₁ , y) (lemma-c-lemma-lemma x (helper Θ) Θ') (interp-lemma2 x (Θ i0))

  lemma-c-lemma : ∀ {Γ Γ' τ} → (x : interp τ) → (Θ : sctx Γ Γ') → (Θ' : interpC Γ) → (interpS Θ Θ' , x) == (interpS (lem2 Θ) (Θ' , x))
  lemma-c-lemma {Γ} {[]} x Θ Θ' = Refl
  lemma-c-lemma {Γ} {A :: Γ'} x Θ Θ' = ap (λ h → h , x) (lemma-c-lemma-lemma x Θ Θ')

  lemma-c-lemma-rec : ∀ {Γ Γ' τ} → (x : interp nat) → (y : interp τ) → (Θ : sctx Γ Γ') → (Θ' : interpC Γ)
                                         → ((interpS Θ Θ' , y) , x) == interpS (lem2 (lem2 Θ)) ((Θ' , y) , x)
  lemma-c-lemma-rec {Γ} {[]} x y Θ Θ' = Refl
  lemma-c-lemma-rec {Γ} {A :: Γ'} x y Θ Θ' = lemma-c-lemma x (lem2 Θ) (Θ' , y) ∘ ap (λ h → h , x) (lemma-c-lemma y Θ Θ')

  lemma-c : ∀ {Γ Γ' τ} (e : Γ' |- τ) → (Θ : sctx Γ Γ') → (Θ' : interpC Γ) → (interpE e) (interpS Θ Θ') == (interpE (subst Θ e)) Θ'
  lemma-c (var i0) b c = Refl
  lemma-c (var (iS x)) b c = lemma-c (var x) (helper b) c
  lemma-c z b c = Refl
  lemma-c (suc e) b c = ap S (lemma-c e b c)
  lemma-c {Γ} {Γ'} {τ} (rec e e0 e1) b c = natrec (interpE e0 (interpS b c))
                                (λ n k → interpE e1 ((interpS b c , k) , n))
                                (interpE e (interpS b c))
                                                      =⟨ ap
                                                        (λ h →
                                                          natrec h (λ n k → interpE e1 ((interpS b c , k) , n))
                                                            (interpE e (interpS b c)))
                                                              (lemma-c e0 b c) ⟩
                              natrec (interpE (subst b e0) c)
                                (λ n k → interpE e1 ((interpS b c , k) , n))
                                (interpE e (interpS b c))
                                                      =⟨ ap
                                                           (λ h →
                                                              natrec (interpE (subst b e0) c)
                                                              (λ n k → interpE e1 ((interpS b c , k) , n)) h)
                                                           (lemma-c e b c) ⟩
                              natrec (interpE (subst b e0) c)
                                (λ n k → interpE e1 ((interpS b c , k) , n))
                                (interpE (subst b e) c) =⟨ ap
                                                             (λ h → natrec (interpE (subst b e0) c) h (interpE (subst b e) c))
                                                               (λ= (λ x →
                                                                 λ= (λ y →
                                                                   ap (λ h → interpE e1 h) (lemma-c-lemma-rec x y b c)))) ⟩
                              natrec (interpE (subst b e0) c)
                                (λ n k → interpE e1 (interpS (lem2 (lem2 b)) ((c , k) , n)))
                                (interpE (subst b e) c) =⟨ ap
                                        (λ h → natrec (interpE (subst b e0) c) h (interpE (subst b e) c)) 
                                          (λ= (λ x → 
                                            λ= (λ y → lemma-c {nat :: τ :: Γ} {nat :: τ :: Γ'} e1 (lem2 (lem2 b)) ((c , y) , x)))) ⟩
                             natrec (interpE (subst b e0) c)
                                 (λ n k → interpE (subst (lem2 (lem2 b)) e1) ((c , k) , n))
                                 (interpE (subst b e) c)
                                                 ∎

  lemma-c {Γ} {Γ'} {ρ ⇒ τ} (lam e) b c = interpE (lam e) (interpS b c) =⟨ Refl ⟩
                        (λ x → interpE e (interpS b c , x)) =⟨ λ= (λ x → ap (λ h → interpE e h) (lemma-c-lemma x b c)) ⟩
                        (λ x → interpE e (interpS (lem2 b) (c , x))) =⟨ λ= (λ x → lemma-c {ρ :: Γ} {ρ :: Γ'} e (lem2 b) (c , x)) ⟩
                        (λ x → interpE (subst (lem2 b) e) (c , x)) ∎
  lemma-c (app e1 e2) b c = interpE (app e1 e2) (interpS b c)                     =⟨ Refl ⟩
                            interpE e1 (interpS b c) (interpE e2 (interpS b c))   =⟨ ap (λ f → f (interpE e2 (interpS b c))) (lemma-c e1 b c) ⟩
                            interpE (subst b e1) c (interpE e2 (interpS b c))     =⟨ ap (λ f → interpE (subst b e1) c f) (lemma-c e2 b c) ⟩
                            interpE (subst b e1) c (interpE (subst b e2) c)       ∎

  -- Soundness: if e >> e' then interp e == interp e'
  sound : ∀ {τ} (e e' : [] |- τ) → e >> e' → (interpE e <>) == (interpE e' <>)
  sound (var x) d ()
  sound z d ()
  sound (suc e) .(suc e') (suc-steps .e e' p) = ap S (sound e e' p)
  sound (rec e e0 e1) .(rec e' e0 e1) (rec-steps .e e' .e0 .e1 p) = ap (natrec (interpE e0 <>) (λ n k → interpE e1 ((<> , k) , n))) (sound e e' p)
  sound (rec .z .d e1) d (rec-steps-z e .d .e1) = Refl
  sound (rec .(suc e) e0 e1) .(subst (lem4 e (rec e e0 e1)) e1) (rec-steps-suc e .e0 .e1 x) = lemma-c e1 (lem4 e (rec e e0 e1)) <>
  sound (lam x) d ()
  sound (app e1 e2) .(app e1' e2) (app-steps .e1 e1' .e2 p) = ap (λ d → d (interpE e2 <>)) (sound e1 e1' p)
  sound (app e1 e2) .(app e1 e2') (app-steps-2 .e1 .e2 e2' x p) = ap (λ d → interpE e1 <> d) (sound e2 e2' p)
  sound (app .(lam e1) e2) .(subst (lem3 e2) e1) (app-steps-3 e1 .e2) = lemma-c e1 (lem3 e2) <>

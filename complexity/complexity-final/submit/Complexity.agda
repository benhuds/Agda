open import Preliminaries

module Complexity where

  data CTp : Set where
    unit : CTp
    nat : CTp -- discrete natural numbers ♭nat, where we interpret ≤ as =
    _->c_ : CTp → CTp → CTp
    _×c_ : CTp → CTp → CTp
    list : CTp → CTp
    bool : CTp
    C : CTp
    rnat : CTp

  data CTpM : CTp → Set where
    runit : CTpM unit
    rnat-max : CTpM rnat
    _×cm_ : ∀ {τ1 τ2} → CTpM τ1 → CTpM τ2 → CTpM (τ1 ×c τ2)
    _->cm_ : ∀ {τ1 τ2} → CTpM τ2 → CTpM (τ1 ->c τ2)
    
  -- represent a context as a list of types
  Ctx = List CTp

  -- de Bruijn indices (for free variables)
  data _∈_ : CTp → Ctx → Set where
    i0 : ∀ {Γ τ}
       → τ ∈ (τ :: Γ)
    iS : ∀ {Γ τ τ1}
       → τ ∈ Γ
       → τ ∈ (τ1 :: Γ)
  
  rctx : Ctx → Ctx → Set
  rctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → τ ∈ Γ
  r-extend : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) (τ :: Γ')
  data _|-_ : Ctx → CTp → Set
  sctx : Ctx → Ctx → Set
  sctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → Γ |- τ
  _∙rr_ : ∀ {A B C} → rctx A B → rctx B C → rctx A C
  _rs_ : ∀ {A B C} → rctx A B → sctx B C → sctx A C
  ren : ∀ {Γ Γ' τ} → Γ' |- τ → rctx Γ Γ' → Γ |- τ
  subst : ∀ {Γ Γ' τ} → Γ' |- τ → sctx Γ Γ' → Γ |- τ
  _ss_ : ∀ {A B C} → sctx A B → sctx B C → sctx A C
  _sr_ : ∀ {A B C} → sctx A B → rctx B C → sctx A C
  data _≤s_ : ∀ {Γ T} → Γ |- T → Γ |- T → Set
  rename-var : ∀ {Γ Γ' τ} → rctx Γ Γ' → τ ∈ Γ' → τ ∈ Γ
  idr : ∀ {Γ} → rctx Γ Γ
  p∙ : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) Γ'
  p : ∀ {Γ τ} → rctx (τ :: Γ) Γ
  rename-var-ident : ∀ {Γ τ} → (x : τ ∈ Γ) → rename-var idr x == x
  rename-var-∙ : ∀ {A B C τ} → (r1 : rctx A B) (r2 : rctx B C) (x : τ ∈ C) → rename-var r1 (rename-var r2 x) == rename-var (r1 ∙rr r2) x
  ∙rr-assoc : ∀ {A B C D} → (r1 : rctx A B) (r2 : rctx B C) (r3 : rctx C D) → _==_ {_} {rctx A D} (r1 ∙rr (r2 ∙rr r3)) ((r1 ∙rr r2) ∙rr r3)
  extend-ren-comp-lemma : ∀ {Γ Γ' Γ'' τ τ'} → (x : τ ∈ τ' :: Γ'') (ρ1 : rctx Γ Γ') (ρ2 : rctx Γ' Γ'') → Id {_} {_} ((r-extend ρ1 ∙rr r-extend ρ2) x) (r-extend (ρ1 ∙rr ρ2) x)
  extend-ren-comp : ∀ {Γ Γ' Γ'' τ} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'') → Id {_} {rctx (τ :: Γ) (τ :: Γ'')} (r-extend ρ1 ∙rr r-extend ρ2) (r-extend (ρ1 ∙rr ρ2))
  wkn : ∀ {Γ τ1 τ2} → Γ |- τ2 → (τ1 :: Γ) |- τ2
  s-extend : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) (τ :: Γ')
  ids : ∀ {Γ} → sctx Γ Γ
  q∙ : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) Γ'
  lem3' : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ |- τ → sctx Γ (τ :: Γ')
  q : ∀ {Γ τ} → Γ |- τ → sctx Γ (τ :: Γ)
  svar : ∀ {Γ1 Γ2 τ} → sctx Γ1 Γ2 → τ ∈ Γ2 → Γ1 |- τ
  lem4' : ∀ {Γ Γ' τ1 τ2} → sctx Γ Γ' → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ'))
  lem4 : ∀ {Γ τ1 τ2} → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ))
  lem5' : ∀ {Γ Γ' τ1 τ2 τ3} → sctx Γ Γ' → Γ |- τ1 → Γ |- τ2 → Γ |- τ3 → sctx Γ (τ1 :: (τ2 :: (τ3 :: Γ')))
  lem5 : ∀ {Γ τ1 τ2 τ3} → Γ |- τ1 → Γ |- τ2 → Γ |- τ3 → sctx Γ (τ1 :: (τ2 :: (τ3 :: Γ)))

  data _|-_ where
    unit : ∀ {Γ} → Γ |- unit
    0C : ∀ {Γ} → Γ |- C
    1C : ∀ {Γ}→ Γ |- C
    plusC : ∀ {Γ} → Γ |- C → Γ |- C → Γ |- C
    var : ∀ {Γ τ} → τ ∈ Γ → Γ |- τ
    z : ∀ {Γ} → Γ |- nat
    s : ∀ {Γ} → (e : Γ |- nat) → Γ |- nat
    rec : ∀ {Γ τ} → Γ |- nat → Γ |- τ → (nat :: (τ :: Γ)) |- τ → Γ |- τ
    lam : ∀ {Γ τ ρ} → (ρ :: Γ) |- τ → Γ |- (ρ ->c τ)
    app : ∀ {Γ τ1 τ2} → Γ |- (τ2 ->c τ1) → Γ |- τ2 → Γ |- τ1
    prod : ∀ {Γ τ1 τ2} → Γ |- τ1 → Γ |- τ2 → Γ |- (τ1 ×c τ2)
    l-proj : ∀ {Γ τ1 τ2} → Γ |- (τ1 ×c τ2) → Γ |- τ1
    r-proj : ∀ {Γ τ1 τ2} → Γ |- (τ1 ×c τ2) → Γ |- τ2
    nil : ∀ {Γ τ} → Γ |- list τ
    _::c_ : ∀ {Γ τ} → Γ |- τ → Γ |- list τ → Γ |- list τ
    listrec : ∀ {Γ τ τ'} → Γ |- list τ → Γ |- τ' → (τ :: (list τ :: (τ' :: Γ))) |- τ' → Γ |- τ'
    true : ∀ {Γ} → Γ |- bool
    false : ∀ {Γ} → Γ |- bool
    max : ∀ {Γ τ} → CTpM τ → Γ |- τ → Γ |- τ  → Γ |- τ
    letc : ∀ {Γ ρ τ} → (ρ :: Γ) |- τ → Γ |- ρ → Γ |- τ

{-[ Θ ]s : Monotone [ Γ ]  [ Γ' ]
  [ ρ ]r : same
  interpE ren e ρ k == interpE e (interpR ρ) k
interp commutes with renaming and substitution
equations that define ren and subst are true in the semantics-}
--also add axioms for max-l/r etc.
  data _≤s_ where
    refl-s : ∀ {Γ T} → {e : Γ |- T} → e ≤s e
    trans-s : ∀ {Γ T} → {e e' e'' : Γ |- T} → e ≤s e' → e' ≤s e'' → e ≤s e''
    cong-refl : ∀ {Γ τ} {e e' : Γ |- τ} → e == e' → e ≤s e'
    lt : ∀ {Γ} → _≤s_ {Γ} 0C 1C
    +-unit-l : ∀ {Γ} {e : Γ |- C} → (plusC 0C e) ≤s e
    +-unit-l' : ∀ {Γ} {e : Γ |- C} → e ≤s (plusC 0C e) 
    +-unit-r : ∀ {Γ} {e : Γ |- C} → (plusC e 0C) ≤s e
    +-unit-r' : ∀ {Γ} {e : Γ |- C} → e ≤s (plusC e 0C) 
    +-assoc : ∀ {Γ} {e1 e2 e3 : Γ |- C} → (plusC e1 (plusC e2 e3)) ≤s (plusC (plusC e1 e2) e3)
    +-assoc' : ∀ {Γ} {e1 e2 e3 : Γ |- C} → (plusC (plusC e1 e2) e3) ≤s (plusC e1 (plusC e2 e3))
    refl-+ : ∀ {Γ} {e0 e1 : Γ |- C} → (plusC e0 e1) ≤s (plusC e1 e0)
    cong-+ : ∀ {Γ} {e0 e1 e0' e1' : Γ |- C} → e0 ≤s e0' → e1 ≤s e1' → (plusC e0 e1) ≤s (plusC e0' e1')    
    cong-lproj : ∀ {Γ τ τ'} {e e' : Γ |- (τ ×c τ')} → e ≤s e' → (l-proj e) ≤s (l-proj e')    
    cong-rproj : ∀ {Γ τ τ'} {e e' : Γ |- (τ ×c τ')} → e ≤s e' → (r-proj e) ≤s (r-proj e')
    cong-app   : ∀ {Γ τ τ'} {e e' : Γ |- (τ ->c τ')} {e1 : Γ |- τ} → e ≤s e' → (app e e1) ≤s (app e' e1)
    ren-cong : ∀ {Γ Γ' τ} {e1 e2 : Γ' |- τ} {ρ : rctx Γ Γ'} → e1 ≤s e2 → (ren e1 ρ) ≤s (ren e2 ρ)
    subst-cong : ∀ {Γ Γ' τ} {e1 e2 : Γ' |- τ} {Θ : sctx Γ Γ'} → e1 ≤s e2 → (subst e1 Θ) ≤s (subst e2 Θ)
    subst-cong2 : ∀ {Γ Γ' τ} {Θ Θ' : sctx Γ Γ'} {e : Γ' |- τ} → (∀ τ → (x : τ ∈ Γ') → Θ x ≤s Θ' x) → subst e Θ ≤s subst e Θ'
    cong-rec : ∀ {Γ τ} {e e' : Γ |- nat} {e0 : Γ |- τ} {e1 : (nat :: (τ :: Γ)) |- τ}
              → e ≤s e' → rec e e0 e1 ≤s rec e' e0 e1
    cong-listrec : ∀ {Γ τ τ'} {e e' : Γ |- list τ} {e0 : Γ |- τ'} {e1 : (τ :: (list τ :: (τ' :: Γ))) |- τ'}
               → e ≤s e' → listrec e e0 e1 ≤s listrec e' e0 e1
    lam-s : ∀ {Γ T T'} → {e : (T :: Γ) |- T'} → {e2 : Γ |- T} → subst e (q e2) ≤s app (lam e) e2
    l-proj-s : ∀ {Γ T1 T2} → {e1 : Γ |- T1}  {e2 : Γ |- T2} → e1 ≤s (l-proj (prod e1 e2))
    r-proj-s : ∀ {Γ T1 T2} → {e1 : Γ |- T1} → {e2 : Γ |- T2} → e2 ≤s (r-proj (prod e1 e2))
    rec-steps-z : ∀ {Γ T} → {e0 : Γ |- T} → {e1 : (nat :: (T :: Γ)) |- T} → e0 ≤s (rec z e0 e1)
    rec-steps-s : ∀ {Γ T} → {e : Γ |- nat} → {e0 : Γ |- T} → {e1 : (nat :: (T :: Γ)) |- T} → subst e1 (lem4 e (rec e e0 e1)) ≤s (rec (s e) e0 e1)
    listrec-steps-nil : ∀ {Γ τ τ'} → {e0 : Γ |- τ'} → {e1 : (τ :: (list τ :: (τ' :: Γ))) |- τ'}
                      → e0 ≤s (listrec nil e0 e1)
    listrec-steps-cons : ∀ {Γ τ τ'} → {h : Γ |- τ} {t : Γ |- list τ}
                       → {e0 : Γ |- τ'} → {e1 : (τ :: (list τ :: (τ' :: Γ))) |- τ'}
                       → subst e1 (lem5 h t (listrec t e0 e1)) ≤s (listrec (h ::c t) e0 e1)
    ren-comp-l : ∀ {Γ Γ' Γ'' τ} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'') → (e : Γ'' |- τ) → (ren (ren e ρ2) ρ1) ≤s (ren e (ρ1 ∙rr ρ2))
    ren-comp-r : ∀ {Γ Γ' Γ'' τ} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'') → (e : Γ'' |- τ) → (ren e (ρ1 ∙rr ρ2)) ≤s (ren (ren e ρ2) ρ1)
    subst-id-l : ∀ {Γ τ} → (e : Γ |- τ) → e ≤s subst e ids
    subst-id-r : ∀ {Γ τ} → (e : Γ |- τ) → subst e ids ≤s e
    subst-rs-l : ∀ {A B C τ} → (ρ : rctx C A) (Θ : sctx A B) (e : B |- τ)
               → ren (subst e Θ) ρ ≤s subst e (ρ rs Θ)
    subst-rs-r : ∀ {A B C τ} → (ρ : rctx C A) (Θ : sctx A B) (e : B |- τ)
               → subst e (ρ rs Θ) ≤s ren (subst e Θ) ρ
    subst-sr-l : ∀ {Γ Γ' Γ'' τ} → (Θ : sctx Γ Γ') → (ρ : rctx Γ' Γ'') → (e : Γ'' |- τ)
              → (subst (ren e ρ) Θ) ≤s subst e (Θ sr ρ)
    subst-sr-r : ∀ {Γ Γ' Γ'' τ} → (Θ : sctx Γ Γ') → (ρ : rctx Γ' Γ'') → (e : Γ'' |- τ)
              → subst e (Θ sr ρ) ≤s (subst (ren e ρ) Θ)
    subst-ss-l : ∀ {A B C τ} → (Θ1 : sctx A B) (Θ2 : sctx B C) (e : C |- τ)
               → subst e (Θ1 ss Θ2) ≤s subst (subst e Θ2) Θ1
    subst-ss-r : ∀ {A B C τ} → (Θ1 : sctx A B) (Θ2 : sctx B C) (e : C |- τ)
               → subst (subst e Θ2) Θ1 ≤s subst e (Θ1 ss Θ2)
    subst-compose-l : ∀ {Γ Γ' τ τ1} (Θ : sctx Γ Γ') (v : Γ |- τ) (e : (τ :: Γ' |- τ1) )
                → subst (subst e (s-extend Θ)) (q v) ≤s subst e (lem3' Θ v)
    subst-compose-r : ∀ {Γ Γ' τ τ1} (Θ : sctx Γ Γ') (v : Γ |- τ) (e : (τ :: Γ' |- τ1) )
                → subst e (lem3' Θ v) ≤s subst (subst e (s-extend Θ)) (q v)
    subst-compose2-l : ∀ {Γ Γ' τ τ1 τ2} (Θ : sctx Γ Γ') (e1 : (τ1 :: (τ2 :: Γ')) |- τ) (v1 : Γ |- τ1) (v2 : Γ |- τ2)
                     → subst (subst e1 (s-extend (s-extend Θ))) (lem4 v1 v2) ≤s subst e1 (lem4' Θ v1 v2)
    subst-compose2-r : ∀ {Γ Γ' τ τ1 τ2} (Θ : sctx Γ Γ') (e1 : (τ1 :: (τ2 :: Γ')) |- τ) (v1 : Γ |- τ1) (v2 : Γ |- τ2)
                     → subst e1 (lem4' Θ v1 v2) ≤s subst (subst e1 (s-extend (s-extend Θ))) (lem4 v1 v2)
    subst-compose3-l : ∀ {Γ Γ' τ τ1 τ2} (Θ : sctx Γ Γ') (e1 : (τ1 :: (τ2 :: Γ')) |- τ) (v1 : Γ' |- τ1) (v2 : Γ' |- τ2)
                     → subst (subst e1 (lem4 v1 v2)) Θ ≤s subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ))
    subst-compose3-r : ∀ {Γ Γ' τ τ1 τ2} (Θ : sctx Γ Γ') (e1 : (τ1 :: (τ2 :: Γ')) |- τ) (v1 : Γ' |- τ1) (v2 : Γ' |- τ2)
                     → subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ)) ≤s subst (subst e1 (lem4 v1 v2)) Θ
    subst-compose4-l : ∀ {Γ Γ' τ} (Θ : sctx Γ Γ') (v' : Γ |- nat) (r : Γ |- τ) (e2 : (nat :: (τ :: Γ')) |- τ)
                     → subst (subst e2 (s-extend (s-extend Θ))) (lem4 v' r) ≤s subst e2 (lem4' Θ v' r)
    subst-compose4-r : ∀ {Γ Γ' τ} (Θ : sctx Γ Γ') (v' : Γ |- nat) (r : Γ |- τ) (e2 : (nat :: (τ :: Γ')) |- τ)
                     → subst e2 (lem4' Θ v' r) ≤s subst (subst e2 (s-extend (s-extend Θ))) (lem4 v' r)
    subst-compose5-l : ∀ {Γ Γ' τ τ1 τ2 τ3} (Θ : sctx Γ Γ') (e : (τ1 :: (τ2 :: (τ3 :: Γ'))) |- τ) (v1 : Γ |- τ1) (v2 : Γ |- τ2) (v3 : Γ |- τ3)
                     → subst (subst e (s-extend (s-extend (s-extend (Θ))))) (lem5 v1 v2 v3) ≤s subst e (lem5' Θ v1 v2 v3)
    subst-compose5-r : ∀ {Γ Γ' τ τ1 τ2 τ3} (Θ : sctx Γ Γ') (e : (τ1 :: (τ2 :: (τ3 :: Γ'))) |- τ) (v1 : Γ |- τ1) (v2 : Γ |- τ2) (v3 : Γ |- τ3)
                     → subst e (lem5' Θ v1 v2 v3) ≤s subst (subst e (s-extend (s-extend (s-extend (Θ))))) (lem5 v1 v2 v3)

  -- r-extend : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) (τ :: Γ')
  r-extend ρ i0 = i0
  r-extend ρ (iS x) = iS (ρ x)
  -- _∙rr_ : ∀ {A B C} → rctx A B → rctx B C → rctx A C
  ρ1 ∙rr ρ2 = ρ1 o ρ2
  rename-var ρ a = ρ a
  idr x = x
  p∙ ρ = λ x → iS (ρ x)
  p = p∙ idr
   --free stuff
  rename-var-ident _ = Refl
  rename-var-∙ _ _ _ = Refl
  ∙rr-assoc r1 r2 r3 = Refl
  
  ren unit ρ = unit
  ren 0C ρ = 0C
  ren 1C ρ = 1C
  ren (plusC e e₁) ρ = plusC (ren e ρ) (ren e₁ ρ)
  ren (var x) ρ = var (ρ x)
  ren z ρ = z
  ren (s e) ρ = s (ren e ρ)
  ren (rec e e₁ e₂) ρ = rec (ren e ρ) (ren e₁ ρ) (ren e₂ (r-extend (r-extend ρ)))
  ren (lam e) ρ = lam (ren e (r-extend ρ))
  ren (app e e₁) ρ = app (ren e ρ) (ren e₁ ρ)
  ren (prod e1 e2) ρ = prod (ren e1 ρ) (ren e2 ρ)
  ren (l-proj e) ρ = l-proj (ren e ρ)
  ren (r-proj e) ρ = r-proj (ren e ρ)
  ren nil ρ = nil
  ren (x ::c xs) ρ = ren x ρ ::c ren xs ρ
  ren true ρ = true
  ren false ρ = false
  ren (listrec e e₁ e₂) ρ = listrec (ren e ρ) (ren e₁ ρ) (ren e₂ (r-extend (r-extend (r-extend ρ))))
  ren (max τ e1 e2) ρ = max τ (ren e1 ρ) (ren e2 ρ)
  ren (letc e e') ρ = letc (ren e (r-extend ρ)) (ren e' ρ)

  extend-ren-comp-lemma i0 ρ1 ρ2 = Refl
  extend-ren-comp-lemma (iS x) ρ1 ρ2 = Refl

  extend-ren-comp ρ1 ρ2 = λ=i (λ τ → λ= (λ x → extend-ren-comp-lemma x ρ1 ρ2))

  -- weakening a context
  wkn e = ren e iS
  -- parallel extension
  s-extend Θ i0 = var i0
  s-extend Θ (iS x) = wkn (Θ x)
  -- identity substitution
  ids x = var x
  -- weakening with substitution
  q∙ Θ = λ x → wkn (Θ x)

  lem3' Θ e i0 = e
  lem3' Θ e (iS i) = Θ i
  --lem3
  q e = lem3' ids e

  -- subst-var
  svar Θ i = q (Θ i) i0

  lem4' Θ a b = lem3' (lem3' Θ b) a

  lem4 e1 e2 = lem4' ids e1 e2

  lem5' Θ a b c = lem3' (lem3' (lem3' Θ c) b) a

  lem5 e1 e2 e3 = lem5' ids e1 e2 e3

  subst unit Θ = unit
  subst 0C Θ = 0C
  subst 1C Θ = 1C
  subst (plusC e e₁) Θ = plusC (subst e Θ) (subst e₁ Θ)
  subst (var x) Θ = Θ x
  subst z Θ = z
  subst (s e) Θ = s (subst e Θ)
  subst (rec e e₁ e₂) Θ = rec (subst e Θ) (subst e₁ Θ) (subst e₂ (s-extend (s-extend Θ)))
  subst (lam e) Θ = lam (subst e (s-extend Θ))
  subst (app e e₁) Θ = app (subst e Θ) (subst e₁ Θ)
  subst (prod e1 e2) Θ = prod (subst e1 Θ) (subst e2 Θ)
  subst (l-proj e) Θ = l-proj (subst e Θ)
  subst (r-proj e) Θ = r-proj (subst e Θ)
  subst nil Θ = nil
  subst (x ::c xs) Θ = subst x Θ ::c subst xs Θ
  subst true Θ = true
  subst false Θ = false
  subst (listrec e e₁ e₂) Θ = listrec (subst e Θ) (subst e₁ Θ) (subst e₂ (s-extend (s-extend (s-extend Θ))))
  subst (max τ e1 e2) Θ = max τ (subst e1 Θ) (subst e2 Θ)
  subst (letc e e') Θ = letc (subst e (s-extend Θ)) (subst e' Θ)
  
  subst1 : ∀ {Γ τ τ1} → Γ |- τ1 → (τ1 :: Γ) |- τ → Γ |- τ
  subst1 e e' = subst e' (q e)

  _rs_ ρ Θ x = ren (subst (var x) Θ) ρ
  _ss_ Θ1 Θ2 x = subst (subst (var x) Θ2) Θ1
  _sr_ Θ ρ x = subst (ren (var x) ρ) Θ

  extend-id-once-lemma : ∀ {Γ τ τ'} → (x : τ ∈ τ' :: Γ) → _==_ {_} {τ' :: Γ |- τ}
                       (ids {τ' :: Γ} {τ} x) (s-extend {Γ} {Γ} {τ'} (ids {Γ}) {τ} x)
  extend-id-once-lemma i0 = Refl
  extend-id-once-lemma (iS x) = Refl

  extend-id-once : ∀ {Γ τ} → Id {_} {sctx (τ :: Γ) (τ :: Γ)} (ids {τ :: Γ}) (s-extend ids)
  extend-id-once = λ=i (λ τ → λ= (λ x → extend-id-once-lemma x))

  extend-id-twice : ∀ {Γ τ1 τ2} → Id {_} {sctx (τ1 :: τ2 :: Γ) (τ1 :: τ2 :: Γ)} (ids {τ1 :: τ2 :: Γ}) (s-extend (s-extend ids))
  extend-id-twice = ap s-extend extend-id-once ∘ extend-id-once

  _+C_ : ∀ {Γ τ} → Γ |- C  → Γ |- (C ×c τ)→ Γ |- (C ×c τ)
  c +C e = prod (plusC c (l-proj e)) (r-proj e)
--letc (prod (l-proj (var i0)) (r-proj (var i0))) e

  _trans_ : ∀ {Γ T}
            → {e e' e'' : Γ |- T}
            → e ≤s e' → e' ≤s e''
            → e ≤s e''
  _trans_ = trans-s
  infixr 10 _trans_


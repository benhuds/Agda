open import Preliminaries
open import Preorder-Max

module Pilot where

  data CTp : Set where
    unit : CTp
    nat : CTp
    _->c_ : CTp → CTp → CTp
    _×c_ : CTp → CTp → CTp
    list : CTp → CTp
    bool : CTp
    C : CTp
    nat≤ : CTp

  -- represent a context as a list of types
  Ctx = List CTp

  -- de Bruijn indices (for free variables)
  data _∈_ : CTp → Ctx → Set where
    i0 : ∀ {Γ τ}
       → τ ∈ (τ :: Γ)
    iS : ∀ {Γ τ τ1}
       → τ ∈ Γ
       → τ ∈ (τ1 :: Γ)

  mutual
    sctx : Ctx → Ctx → Set
    sctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → Γ |- τ

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
      z' : ∀ {Γ} → Γ |- nat≤
      suc' : ∀ {Γ}
         → Γ |- nat≤
         → Γ |- nat≤
      rec' : ∀ {Γ τ}
         → Γ |- nat≤ 
         → (Z' : Γ |- τ)
         → (S' : (nat≤ :: (τ :: Γ)) |- τ)
         → (P : Z' ≤s subst S' (lem3' (lem3' ids Z') z'))
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
      nil : ∀ {Γ τ} → Γ |- list τ
      _::c_ : ∀ {Γ τ} → Γ |- τ → Γ |- list τ → Γ |- list τ
      listrec : ∀ {Γ τ τ'} → Γ |- list τ → Γ |- τ' → (τ :: (list τ :: (τ' :: Γ))) |- τ' → Γ |- τ'
      true : ∀ {Γ} → Γ |- bool
      false : ∀ {Γ} → Γ |- bool
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
      cong-subst : ∀ {Γ Γ' τ} {e1 e2 : Γ' |- τ} {Θ : sctx Γ Γ'} → e1 ≤s e2 → (subst e1 Θ) ≤s (subst e2 Θ)
      subst-s : ∀ {Γ Γ' τ} {Θ Θ' : sctx Γ Γ'} {e : Γ' |- τ} → (∀ τ → (x : τ ∈ Γ') → Θ x ≤s Θ' x) → subst e Θ ≤s subst e Θ'
      cong-rec : ∀ {Γ τ} {e e' : Γ |- nat} {e0 : Γ |- τ} {e1 : (nat :: (τ :: Γ)) |- τ}
             → e ≤s e'
             → rec e e0 e1 ≤s rec e' e0 e1
      cong-listrec : ∀ {Γ τ τ'} {e e' : Γ |- list τ} {e0 : Γ |- τ'} {e1 : (τ :: (list τ :: (τ' :: Γ))) |- τ'}
                 → e ≤s e'
                 → listrec e e0 e1 ≤s listrec e' e0 e1
   -- lam-s : ∀ {Γ T T'}
    --      → {e : (T :: Γ) |- T'}
      --    → {e2 : Γ |- T}
        --  → subst e (q e2) ≤s app (lam e) e2
      l-proj-s : ∀ {Γ T1 T2}
             → {e1 : Γ |- T1}  {e2 : Γ |- T2}
             → e1 ≤s (l-proj (prod e1 e2))
      r-proj-s : ∀ {Γ T1 T2}
             → {e1 : Γ |- T1} → {e2 : Γ |- T2}
             → e2 ≤s (r-proj (prod e1 e2))
      rec-steps-z : ∀ {Γ T}
                → {e0 : Γ |- T}
                → {e1 : (nat :: (T :: Γ)) |- T}
                → e0 ≤s (rec z e0 e1)
      rec-steps-s : ∀ {Γ T}
                  → {e : Γ |- nat}
                  → {e0 : Γ |- T}
                  → {e1 : (nat :: (T :: Γ)) |- T}
                  → subst e1 (lem4 e (rec e e0 e1)) ≤s (rec (suc e) e0 e1)
      listrec-steps-nil : ∀ {Γ τ τ'}
                      → {e0 : Γ |- τ'}
                      → {e1 : (τ :: (list τ :: (τ' :: Γ))) |- τ'}
                      → e0 ≤s (listrec nil e0 e1)
      listrec-steps-cons : ∀ {Γ τ τ'}
                         → {h : Γ |- τ} {t : Γ |- list τ}
                         → {e0 : Γ |- τ'}
                         → {e1 : (τ :: (list τ :: (τ' :: Γ))) |- τ'}
                         → subst e1 (lem5 h t (listrec t e0 e1)) ≤s (listrec (h ::c t) e0 e1)
    rctx : Ctx → Ctx → Set
    rctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → τ ∈ Γ

    rename-var : ∀ {Γ Γ' τ} → rctx Γ Γ' → τ ∈ Γ' → τ ∈ Γ
    rename-var ρ a = ρ a

    idr : ∀ {Γ} → rctx Γ Γ
    idr x = x

    p∙ : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) Γ'
    p∙ ρ = λ x → iS (ρ x)

    p : ∀ {Γ τ} → rctx (τ :: Γ) Γ
    p = p∙ idr

    _∙rr_ : ∀ {A B C} → rctx A B → rctx B C → rctx A C
    ρ1 ∙rr ρ2 = ρ1 o ρ2

  -- free stuff
    rename-var-ident : ∀ {Γ τ} → (x : τ ∈ Γ) → rename-var idr x == x
    rename-var-ident _ = Refl

    rename-var-∙ : ∀ {A B C τ} → (r1 : rctx A B) (r2 : rctx B C) (x : τ ∈ C)
                 → rename-var r1 (rename-var r2 x) == rename-var (r1 ∙rr r2) x
    rename-var-∙ _ _ _ = Refl

    ∙rr-assoc : ∀ {A B C D} → (r1 : rctx A B) (r2 : rctx B C) (r3 : rctx C D) → _==_ {_} {rctx A D} (r1 ∙rr (r2 ∙rr r3)) ((r1 ∙rr r2) ∙rr r3)
    ∙rr-assoc r1 r2 r3 = Refl

    r-extend : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) (τ :: Γ')
    r-extend ρ i0 = i0
    r-extend ρ (iS x) = iS (ρ x)
  
    ren : ∀ {Γ Γ' τ} → Γ' |- τ → rctx Γ Γ' → Γ |- τ
    ren unit ρ = unit
    ren 0C ρ = 0C
    ren 1C ρ = 1C
    ren (plusC e e₁) ρ = plusC (ren e ρ) (ren e₁ ρ)
    ren (var x) ρ = var (ρ x)
    ren z ρ = z
    ren (suc e) ρ = suc (ren e ρ)
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
    ren z' ρ = z'
    ren (suc' e) ρ = suc' (ren e ρ)
    ren (rec' e e₁ e₂ p) ρ = rec' (ren e ρ) (ren e₁ ρ) (ren e₂ (r-extend (r-extend ρ))) {!!}

{-    extend-ren-comp-lemma : ∀ {Γ Γ' Γ'' τ τ'} → (x : τ ∈ τ' :: Γ'') (ρ1 : rctx Γ Γ') (ρ2 : rctx Γ' Γ'')
                          → Id {_} {_} ((r-extend ρ1 ∙rr r-extend ρ2) x) (r-extend (ρ1 ∙rr ρ2) x)
    extend-ren-comp-lemma i0 ρ1 ρ2 = Refl
    extend-ren-comp-lemma (iS x) ρ1 ρ2 = Refl
  
    extend-ren-comp : ∀ {Γ Γ' Γ'' τ} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'')
                    → Id {_} {rctx (τ :: Γ) (τ :: Γ'')} (r-extend ρ1 ∙rr r-extend ρ2) (r-extend (ρ1 ∙rr ρ2))
    extend-ren-comp ρ1 ρ2 = λ=i (λ τ → λ= (λ x → extend-ren-comp-lemma x ρ1 ρ2))
  
    ren-comp : ∀ {Γ Γ' Γ'' τ} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'') → (e : Γ'' |- τ)
             → (ren (ren e ρ2) ρ1) == (ren e (ρ1 ∙rr ρ2))
    ren-comp ρ1 ρ2 unit = Refl
    ren-comp ρ1 ρ2 0C = Refl
    ren-comp ρ1 ρ2 1C = Refl
    ren-comp ρ1 ρ2 (plusC e e₁) = ap2 plusC (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
    ren-comp ρ1 ρ2 (var x) = ap var (rename-var-∙ ρ1 ρ2 x)
    ren-comp ρ1 ρ2 z = Refl
    ren-comp ρ1 ρ2 (suc e) = ap suc (ren-comp ρ1 ρ2 e)
    ren-comp ρ1 ρ2 (rec e e₁ e₂) = ap3 rec (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
                                       (ap (ren e₂) (ap r-extend (extend-ren-comp ρ1 ρ2) ∘
                                         extend-ren-comp (r-extend ρ1) (r-extend ρ2)) ∘
                                         ren-comp (r-extend (r-extend ρ1)) (r-extend (r-extend ρ2)) e₂)
    ren-comp ρ1 ρ2 (lam e) = ap lam ((ap (ren e) (extend-ren-comp ρ1 ρ2)) ∘ ren-comp (r-extend ρ1) (r-extend ρ2) e)
    ren-comp ρ1 ρ2 (app e e₁) = ap2 app (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
    ren-comp ρ1 ρ2 (prod e e₁) = ap2 prod (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
    ren-comp ρ1 ρ2 (l-proj e) = ap l-proj (ren-comp ρ1 ρ2 e)
    ren-comp ρ1 ρ2 (r-proj e) = ap r-proj (ren-comp ρ1 ρ2 e)
    ren-comp ρ1 ρ2 nil = Refl
    ren-comp ρ1 ρ2 (e ::c e₁) = ap2 _::c_ (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
    ren-comp ρ1 ρ2 (listrec e e₁ e₂) = ap3 listrec (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
                                           (ap (ren e₂) (ap r-extend (ap r-extend (extend-ren-comp ρ1 ρ2)) ∘
                                           (ap r-extend (extend-ren-comp (r-extend ρ1) (r-extend ρ2)) ∘
                                           extend-ren-comp (r-extend (r-extend ρ1)) (r-extend (r-extend ρ2)))) ∘
                                           ren-comp (r-extend (r-extend (r-extend ρ1)))
                                                    (r-extend (r-extend (r-extend ρ2))) e₂)
    ren-comp ρ1 ρ2 true = Refl
    ren-comp ρ1 ρ2 false = Refl
  -}
  -- weakening a context
    wkn : ∀ {Γ τ1 τ2} → Γ |- τ2 → (τ1 :: Γ) |- τ2
    wkn e = ren e iS

    --lem2 (addvar)
    s-extend : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) (τ :: Γ')
    s-extend Θ i0 = var i0
    s-extend Θ (iS x) = wkn (Θ x)

    ids : ∀ {Γ} → sctx Γ Γ
    ids x = var x

    -- weakening with substitution
    q∙ : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) Γ'
    q∙ Θ = λ x → wkn (Θ x)

    lem3' : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ |- τ → sctx Γ (τ :: Γ')
    lem3' Θ e i0 = e
    lem3' Θ e (iS i) = Θ i

    --lem3
    q : ∀ {Γ τ} → Γ |- τ → sctx Γ (τ :: Γ)
    q e = lem3' ids e

  -- subst-var
    svar : ∀ {Γ1 Γ2 τ} → sctx Γ1 Γ2 → τ ∈ Γ2 → Γ1 |- τ
    svar Θ i = q (Θ i) i0
    
    lem4' : ∀ {Γ Γ' τ1 τ2} → sctx Γ Γ' → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ'))
    lem4' Θ a b = lem3' (lem3' Θ b) a

    lem4 : ∀ {Γ τ1 τ2} → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ))
    lem4 e1 e2 = lem4' ids e1 e2

    lem5' : ∀ {Γ Γ' τ1 τ2 τ3} → sctx Γ Γ' → Γ |- τ1 → Γ |- τ2 → Γ |- τ3 → sctx Γ (τ1 :: (τ2 :: (τ3 :: Γ')))
    lem5' Θ a b c = lem3' (lem3' (lem3' Θ c) b) a

    lem5 : ∀ {Γ τ1 τ2 τ3} → Γ |- τ1 → Γ |- τ2 → Γ |- τ3 → sctx Γ (τ1 :: (τ2 :: (τ3 :: Γ)))
    lem5 e1 e2 e3 = lem5' ids e1 e2 e3

    {-# NO_TERMINATION_CHECK #-}
    subst : ∀ {Γ Γ' τ} → Γ' |- τ → sctx Γ Γ' → Γ |- τ
    subst unit Θ = unit
    subst 0C Θ = 0C
    subst 1C Θ = 1C
    subst (plusC e e₁) Θ = plusC (subst e Θ) (subst e₁ Θ)
    subst (var x) Θ = Θ x
    subst z Θ = z
    subst (suc e) Θ = suc (subst e Θ)
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
    subst z' Θ = z'
    subst (suc' e) Θ = suc' (subst e Θ)
    subst (rec' e e₁ e₂ p) Θ = rec' (subst e Θ) (subst e₁ Θ) (subst e₂ (s-extend (s-extend Θ))) (transport (λ x → x) {!!} (subst-s {e = e} (λ τ x → {!!})))
                               --(transport (λ x → x) {!!} (subst-s {e = e} (λ τ x → {!!})))


------weakening and substitution lemmas

      -- renaming = variable for variable substitution
      --functional view:
      --avoids induction,
      --some associativity/unit properties for free

  -- read: you can rename Γ' as Γ
{-
  rename-var : ∀ {Γ Γ' τ} → rctx Γ Γ' → τ ∈ Γ' → τ ∈ Γ
  rename-var ρ a = ρ a

  idr : ∀ {Γ} → rctx Γ Γ
  idr x = x

  -- weakening with renaming
  p∙ : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) Γ'
  p∙ ρ = λ x → iS (ρ x)

  p : ∀ {Γ τ} → rctx (τ :: Γ) Γ
  p = p∙ idr

  _∙rr_ : ∀ {A B C} → rctx A B → rctx B C → rctx A C
  ρ1 ∙rr ρ2 = ρ1 o ρ2

  -- free stuff
  rename-var-ident : ∀ {Γ τ} → (x : τ ∈ Γ) → rename-var idr x == x
  rename-var-ident _ = Refl

  rename-var-∙ : ∀ {A B C τ} → (r1 : rctx A B) (r2 : rctx B C) (x : τ ∈ C)
              → rename-var r1 (rename-var r2 x) == rename-var (r1 ∙rr r2) x
  rename-var-∙ _ _ _ = Refl

  ∙rr-assoc : ∀ {A B C D} → (r1 : rctx A B) (r2 : rctx B C) (r3 : rctx C D) → _==_ {_} {rctx A D} (r1 ∙rr (r2 ∙rr r3)) ((r1 ∙rr r2) ∙rr r3)
  ∙rr-assoc r1 r2 r3 = Refl

  r-extend : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) (τ :: Γ')
  r-extend ρ i0 = i0
  r-extend ρ (iS x) = iS (ρ x)

  ren : ∀ {Γ Γ' τ} → Γ' |- τ → rctx Γ Γ' → Γ |- τ
  ren unit ρ = unit
  ren 0C ρ = 0C
  ren 1C ρ = 1C
  ren (plusC e e₁) ρ = plusC (ren e ρ) (ren e₁ ρ)
  ren (var x) ρ = var (ρ x)
  ren z ρ = z
  ren (suc e) ρ = suc (ren e ρ)
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
  ren z' ρ = z'
  ren (suc' e) ρ = suc' (ren e ρ)
  ren (rec' e e₁ e₂ p) ρ = {!!}
-}
{-
  extend-ren-comp-lemma : ∀ {Γ Γ' Γ'' τ τ'} → (x : τ ∈ τ' :: Γ'') (ρ1 : rctx Γ Γ') (ρ2 : rctx Γ' Γ'')
                        → Id {_} {_} ((r-extend ρ1 ∙rr r-extend ρ2) x) (r-extend (ρ1 ∙rr ρ2) x)
  extend-ren-comp-lemma i0 ρ1 ρ2 = Refl
  extend-ren-comp-lemma (iS x) ρ1 ρ2 = Refl

  extend-ren-comp : ∀ {Γ Γ' Γ'' τ} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'')
                  → Id {_} {rctx (τ :: Γ) (τ :: Γ'')} (r-extend ρ1 ∙rr r-extend ρ2) (r-extend (ρ1 ∙rr ρ2))
  extend-ren-comp ρ1 ρ2 = λ=i (λ τ → λ= (λ x → extend-ren-comp-lemma x ρ1 ρ2))

  ren-comp : ∀ {Γ Γ' Γ'' τ} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'') → (e : Γ'' |- τ)
           → (ren (ren e ρ2) ρ1) == (ren e (ρ1 ∙rr ρ2))
  ren-comp ρ1 ρ2 unit = Refl
  ren-comp ρ1 ρ2 0C = Refl
  ren-comp ρ1 ρ2 1C = Refl
  ren-comp ρ1 ρ2 (plusC e e₁) = ap2 plusC (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
  ren-comp ρ1 ρ2 (var x) = ap var (rename-var-∙ ρ1 ρ2 x)
  ren-comp ρ1 ρ2 z = Refl
  ren-comp ρ1 ρ2 (suc e) = ap suc (ren-comp ρ1 ρ2 e)
  ren-comp ρ1 ρ2 (rec e e₁ e₂) = ap3 rec (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
                                     (ap (ren e₂) (ap r-extend (extend-ren-comp ρ1 ρ2) ∘
                                       extend-ren-comp (r-extend ρ1) (r-extend ρ2)) ∘
                                       ren-comp (r-extend (r-extend ρ1)) (r-extend (r-extend ρ2)) e₂)
  ren-comp ρ1 ρ2 (lam e) = ap lam ((ap (ren e) (extend-ren-comp ρ1 ρ2)) ∘ ren-comp (r-extend ρ1) (r-extend ρ2) e)
  ren-comp ρ1 ρ2 (app e e₁) = ap2 app (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
  ren-comp ρ1 ρ2 (prod e e₁) = ap2 prod (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
  ren-comp ρ1 ρ2 (l-proj e) = ap l-proj (ren-comp ρ1 ρ2 e)
  ren-comp ρ1 ρ2 (r-proj e) = ap r-proj (ren-comp ρ1 ρ2 e)
  ren-comp ρ1 ρ2 nil = Refl
  ren-comp ρ1 ρ2 (e ::c e₁) = ap2 _::c_ (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
  ren-comp ρ1 ρ2 (listrec e e₁ e₂) = ap3 listrec (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
                                       (ap (ren e₂) (ap r-extend (ap r-extend (extend-ren-comp ρ1 ρ2)) ∘
                                       (ap r-extend (extend-ren-comp (r-extend ρ1) (r-extend ρ2)) ∘
                                       extend-ren-comp (r-extend (r-extend ρ1)) (r-extend (r-extend ρ2)))) ∘
                                       ren-comp (r-extend (r-extend (r-extend ρ1)))
                                                (r-extend (r-extend (r-extend ρ2))) e₂)
  ren-comp ρ1 ρ2 true = Refl
  ren-comp ρ1 ρ2 false = Refl

  -- weakening a context
  wkn : ∀ {Γ τ1 τ2} → Γ |- τ2 → (τ1 :: Γ) |- τ2
  wkn e = ren e iS

  sctx : Ctx → Ctx → Set
  sctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → Γ |- τ

  --lem2 (addvar)
  s-extend : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) (τ :: Γ')
  s-extend Θ i0 = var i0
  s-extend Θ (iS x) = wkn (Θ x)

  ids : ∀ {Γ} → sctx Γ Γ
  ids x = var x

    -- weakening with substitution
  q∙ : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) Γ'
  q∙ Θ = λ x → wkn (Θ x)

  lem3' : ∀ {Γ Γ' τ} → sctx Γ Γ' → Γ |- τ → sctx Γ (τ :: Γ')
  lem3' Θ e i0 = e
  lem3' Θ e (iS i) = Θ i

    --lem3
  q : ∀ {Γ τ} → Γ |- τ → sctx Γ (τ :: Γ)
  q e = lem3' ids e

  -- subst-var
  svar : ∀ {Γ1 Γ2 τ} → sctx Γ1 Γ2 → τ ∈ Γ2 → Γ1 |- τ
  svar Θ i = q (Θ i) i0

  lem4' : ∀ {Γ Γ' τ1 τ2} → sctx Γ Γ' → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ'))
  lem4' Θ a b = lem3' (lem3' Θ b) a

  lem4 : ∀ {Γ τ1 τ2} → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ))
  lem4 e1 e2 = lem4' ids e1 e2

  lem5' : ∀ {Γ Γ' τ1 τ2 τ3} → sctx Γ Γ' → Γ |- τ1 → Γ |- τ2 → Γ |- τ3 → sctx Γ (τ1 :: (τ2 :: (τ3 :: Γ')))
  lem5' Θ a b c = lem3' (lem3' (lem3' Θ c) b) a

  lem5 : ∀ {Γ τ1 τ2 τ3} → Γ |- τ1 → Γ |- τ2 → Γ |- τ3 → sctx Γ (τ1 :: (τ2 :: (τ3 :: Γ)))
  lem5 e1 e2 e3 = lem5' ids e1 e2 e3

  subst : ∀ {Γ Γ' τ} → Γ' |- τ → sctx Γ Γ' → Γ |- τ
  subst unit Θ = unit
  subst 0C Θ = 0C
  subst 1C Θ = 1C
  subst (plusC e e₁) Θ = plusC (subst e Θ) (subst e₁ Θ)
  subst (var x) Θ = Θ x
  subst z Θ = z
  subst (suc e) Θ = suc (subst e Θ)
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
-}

  _+C_ : ∀ {Γ τ} → Γ |- C  → Γ |- (C ×c τ)→ Γ |- (C ×c τ)
  c +C e = prod (plusC c (l-proj e)) (r-proj e)

  _trans_ : ∀ {Γ T}
            → {e e' e'' : Γ |- T}
            → e ≤s e' → e' ≤s e''
            → e ≤s e''
  _trans_ = trans-s
  infixr 10 _trans_


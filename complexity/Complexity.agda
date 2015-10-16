{- COMPLEXITY LANGUAGE -}

open import Preliminaries
open import Preorder-Max

module Complexity where

  data CTp : Set where
    unit : CTp
    nat : CTp
    _->c_ : CTp → CTp → CTp
    _×c_ : CTp → CTp → CTp
    list : CTp → CTp
    bool : CTp
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
    nil : ∀ {Γ τ} → Γ |- list τ
    _::c_ : ∀ {Γ τ} → Γ |- τ → Γ |- list τ → Γ |- list τ
    listrec : ∀ {Γ τ τ'} → Γ |- list τ → Γ |- τ' → (τ :: (list τ :: (τ' :: Γ))) |- τ' → Γ |- τ'
    true : ∀ {Γ} → Γ |- bool
    false : ∀ {Γ} → Γ |- bool

  _+C_ : ∀ {Γ τ} → Γ |- C  → Γ |- (C ×c τ)→ Γ |- (C ×c τ)
  c +C e = prod (plusC c (l-proj e)) (r-proj e)

------weakening and substitution lemmas

      -- renaming = variable for variable substitution
      --functional view:
      --avoids induction,
      --some associativity/unit properties for free

  -- read: you can rename Γ' as Γ
  rctx : Ctx → Ctx → Set
  rctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → τ ∈ Γ

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

  subst1 : ∀ {Γ τ τ1} → Γ |- τ1 → (τ1 :: Γ) |- τ → Γ |- τ
  subst1 e e' = subst e' (q e)

  _rs_ : ∀ {A B C} → rctx A B → sctx B C → sctx A C
  _rs_ ρ Θ x = ren (subst (var x) Θ) ρ

  _ss_ : ∀ {A B C} → sctx A B → sctx B C → sctx A C
  _ss_ Θ1 Θ2 x = subst (subst (var x) Θ2) Θ1

  _sr_ : ∀ {A B C} → sctx A B → rctx B C → sctx A C
  _sr_ Θ ρ x = subst (ren (var x) ρ) Θ

  --free stuff
  svar-rs : ∀ {A B C τ} (ρ : rctx A B) (Θ : sctx B C) (x : τ ∈ C)
          → svar (ρ rs Θ) x == ren (svar Θ x) ρ
  svar-rs = λ ρ Θ x → Refl

  svar-ss : ∀ {A B C τ} (Θ1 : sctx A B) (Θ2 : sctx B C) (x : τ ∈ C)
          → svar (Θ1 ss Θ2) x == subst (svar Θ2 x) Θ1
  svar-ss = λ Θ1 Θ2 x → Refl

  svar-sr : ∀ {A B C τ} (Θ : sctx A B) (ρ : rctx B C) (x : τ ∈ C)
          → svar Θ (rename-var ρ x) == svar (Θ sr ρ) x
  svar-sr = λ Θ ρ x → Refl

  svar-id : ∀ {Γ τ} → (x : τ ∈ Γ) → var x == svar ids x
  svar-id = λ x → Refl

  rsr-assoc : ∀ {A B C D} → (ρ1 : rctx A B) (Θ : sctx B C) (ρ2 : rctx C D)
            → Id {_} {sctx A D} ((ρ1 rs Θ) sr ρ2) (ρ1 rs (Θ sr ρ2))
  rsr-assoc = λ ρ1 Θ ρ2 → Refl

  extend-id-once-lemma : ∀ {Γ τ τ'} → (x : τ ∈ τ' :: Γ) → _==_ {_} {τ' :: Γ |- τ}
                       (ids {τ' :: Γ} {τ} x) (s-extend {Γ} {Γ} {τ'} (ids {Γ}) {τ} x)
  extend-id-once-lemma i0 = Refl
  extend-id-once-lemma (iS x) = Refl

  extend-id-once : ∀ {Γ τ} → Id {_} {sctx (τ :: Γ) (τ :: Γ)} (ids {τ :: Γ}) (s-extend ids)
  extend-id-once = λ=i (λ τ → λ= (λ x → extend-id-once-lemma x))

  extend-id-twice : ∀ {Γ τ1 τ2} → Id {_} {sctx (τ1 :: τ2 :: Γ) (τ1 :: τ2 :: Γ)} (ids {τ1 :: τ2 :: Γ}) (s-extend (s-extend ids))
  extend-id-twice = ap s-extend extend-id-once ∘ extend-id-once

  subst-id : ∀ {Γ τ} (e : Γ |- τ) → e == subst e ids
  subst-id unit = Refl
  subst-id 0C = Refl
  subst-id 1C = Refl
  subst-id (plusC e e₁) = ap2 plusC (subst-id e) (subst-id e₁)
  subst-id (var x) = svar-id x
  subst-id z = Refl
  subst-id (suc e) = ap suc (subst-id e)
  subst-id (rec e e₁ e₂) = ap3 rec (subst-id e) (subst-id e₁) (ap (subst e₂) extend-id-twice ∘ subst-id e₂)
  subst-id (lam e) = ap lam (ap (subst e) extend-id-once ∘ subst-id e)
  subst-id (app e e₁) = ap2 app (subst-id e) (subst-id e₁)
  subst-id (prod e e₁) = ap2 prod (subst-id e) (subst-id e₁)
  subst-id (l-proj e) = ap l-proj (subst-id e)
  subst-id (r-proj e) = ap r-proj (subst-id e)
  subst-id nil = Refl
  subst-id (e ::c e₁) = ap2 _::c_ (subst-id e) (subst-id e₁)
  subst-id true = Refl
  subst-id false = Refl
  subst-id (listrec e e₁ e₂) = ap3 listrec (subst-id e) (subst-id e₁) (ap (subst e₂) (ap s-extend (ap s-extend extend-id-once) ∘ extend-id-twice) ∘ subst-id e₂)

  extend-rs-once-lemma : ∀ {A B C τ τ'} → (x : τ ∈ τ' :: B) (ρ : rctx C A) (Θ : sctx A B) → _==_ {_} {τ' :: C |- τ}
                       (_rs_ {τ' :: C} {τ' :: A} {τ' :: B} (r-extend {C} {A} {τ'} ρ)
                         (s-extend {A} {B} {τ'} Θ) {τ} x)
                         (s-extend {C} {B} {τ'} (_rs_ {C} {A} {B} ρ Θ) {τ} x)
  extend-rs-once-lemma i0 ρ Θ = Refl
  extend-rs-once-lemma (iS x) ρ Θ = ! (ren-comp iS ρ (Θ x)) ∘ ren-comp (r-extend ρ) iS (Θ x)

  extend-rs-once : ∀ {A B C τ} → (ρ : rctx C A) (Θ : sctx A B)
                 → Id {_} {sctx (τ :: C) (τ :: B)} (r-extend ρ rs s-extend Θ) (s-extend (ρ rs Θ))
  extend-rs-once ρ Θ = λ=i (λ τ → λ= (λ x → extend-rs-once-lemma x ρ Θ))

  extend-rs-twice : ∀ {A B C τ τ'} → (ρ : rctx C A) (Θ : sctx A B)
                  → Id {_} {sctx (τ :: τ' :: C) (τ :: τ' :: B)} ((r-extend (r-extend ρ)) rs (s-extend (s-extend Θ))) ((s-extend (s-extend (ρ rs Θ))))
  extend-rs-twice ρ Θ = ap s-extend (extend-rs-once ρ Θ) ∘ extend-rs-once (r-extend ρ) (s-extend Θ)

  subst-rs : ∀ {A B C τ} → (ρ : rctx C A) (Θ : sctx A B) (e : B |- τ)
           → ren (subst e Θ) ρ == subst e (ρ rs Θ)
  subst-rs ρ Θ unit = Refl
  subst-rs ρ Θ 0C = Refl
  subst-rs ρ Θ 1C = Refl
  subst-rs ρ Θ (plusC e e₁) = ap2 plusC (subst-rs ρ Θ e) (subst-rs ρ Θ e₁)
  subst-rs ρ Θ (var x) = svar-rs ρ Θ x
  subst-rs ρ Θ z = Refl
  subst-rs ρ Θ (suc e) = ap suc (subst-rs ρ Θ e)
  subst-rs ρ Θ (rec e e₁ e₂) = ap3 rec (subst-rs ρ Θ e) (subst-rs ρ Θ e₁)
                                 (ap (subst e₂) (extend-rs-twice ρ Θ) ∘
                                 subst-rs (r-extend (r-extend ρ)) (s-extend (s-extend Θ)) e₂)
  subst-rs ρ Θ (lam e) = ap lam (ap (subst e) (extend-rs-once ρ Θ) ∘ subst-rs (r-extend ρ) (s-extend Θ) e)
  subst-rs ρ Θ (app e e₁) = ap2 app (subst-rs ρ Θ e) (subst-rs ρ Θ e₁)
  subst-rs ρ Θ (prod e e₁) = ap2 prod (subst-rs ρ Θ e) (subst-rs ρ Θ e₁)
  subst-rs ρ Θ (l-proj e) = ap l-proj (subst-rs ρ Θ e)
  subst-rs ρ Θ (r-proj e) = ap r-proj (subst-rs ρ Θ e)
  subst-rs ρ Θ nil = Refl
  subst-rs ρ Θ (e ::c e₁) = ap2 _::c_ (subst-rs ρ Θ e) (subst-rs ρ Θ e₁)
  subst-rs ρ Θ true = Refl
  subst-rs ρ Θ false = Refl
  subst-rs ρ Θ (listrec e e₁ e₂) = ap3 listrec (subst-rs ρ Θ e) (subst-rs ρ Θ e₁)
                                       (ap (subst e₂) (ap s-extend (ap s-extend (extend-rs-once ρ Θ)) ∘
                                       extend-rs-twice (r-extend ρ) (s-extend Θ)) ∘
                                       subst-rs (r-extend (r-extend (r-extend ρ))) (s-extend (s-extend (s-extend Θ))) e₂)

  rs-comp : ∀ {Γ Γ' Γ'' τ} → (ρ : rctx Γ Γ') → (Θ : sctx Γ' Γ'') → (e : Γ'' |- τ)
          → (ren (subst e Θ) ρ) == subst e (ρ rs Θ)
  rs-comp ρ Θ unit = Refl
  rs-comp ρ Θ 0C = Refl
  rs-comp ρ Θ 1C = Refl
  rs-comp ρ Θ (plusC e e₁) = ap2 plusC (rs-comp ρ Θ e) (rs-comp ρ Θ e₁)
  rs-comp ρ Θ (var x) = svar-rs ρ Θ x
  rs-comp ρ Θ z = Refl
  rs-comp ρ Θ (suc e) = ap suc (rs-comp ρ Θ e)
  rs-comp ρ Θ (rec e e₁ e₂) = ap3 rec (rs-comp ρ Θ e) (rs-comp ρ Θ e₁)
                              (ap (subst e₂) (extend-rs-twice ρ Θ) ∘ rs-comp (r-extend (r-extend ρ)) (s-extend (s-extend Θ)) e₂)
  rs-comp ρ Θ (lam e) = ap lam (ap (subst e) (extend-rs-once ρ Θ) ∘ rs-comp (r-extend ρ) (s-extend Θ) e)
  rs-comp ρ Θ (app e e₁) = ap2 app (rs-comp ρ Θ e) (rs-comp ρ Θ e₁)
  rs-comp ρ Θ (prod e e₁) = ap2 prod (rs-comp ρ Θ e) (rs-comp ρ Θ e₁)
  rs-comp ρ Θ (l-proj e) = ap l-proj (rs-comp ρ Θ e)
  rs-comp ρ Θ (r-proj e) = ap r-proj (rs-comp ρ Θ e)
  rs-comp ρ Θ nil = Refl
  rs-comp ρ Θ (e ::c e₁) = ap2 _::c_ (rs-comp ρ Θ e) (rs-comp ρ Θ e₁)
  rs-comp ρ Θ (listrec e e₁ e₂) = ap3 listrec (rs-comp ρ Θ e) (rs-comp ρ Θ e₁) 
                                    (ap (subst e₂) (ap s-extend (ap s-extend (extend-rs-once ρ Θ)) ∘
                                    extend-rs-twice (r-extend ρ) (s-extend Θ)) ∘
                                    rs-comp (r-extend (r-extend (r-extend ρ)))
                                    (s-extend (s-extend (s-extend Θ))) e₂)
  rs-comp ρ Θ true = Refl
  rs-comp ρ Θ false = Refl

  extend-sr-once-lemma : ∀ {A B C τ τ'} → (Θ : sctx A B) (ρ : rctx B C) (x : τ ∈ τ' :: C)
                       → _==_ {_} {τ' :: A |- τ} (s-extend (_sr_ Θ ρ) x) (_sr_ (s-extend Θ) (r-extend ρ) x)
  extend-sr-once-lemma Θ ρ i0 = Refl
  extend-sr-once-lemma Θ ρ (iS x) = Refl

  extend-sr-once : ∀ {A B C τ} → (Θ : sctx A B) (ρ : rctx B C)
                 → Id {_} {sctx (τ :: A) (τ :: C)} (s-extend Θ sr r-extend ρ) (s-extend (Θ sr ρ))
  extend-sr-once Θ ρ = λ=i (λ τ → λ= (λ x → ! (extend-sr-once-lemma Θ ρ x)))

  extend-sr-twice : ∀ {A B C τ τ'} → (Θ : sctx A B) (ρ : rctx B C)
                 → Id {_} {sctx (τ' :: τ :: A) (τ' :: τ :: C)}
                   (s-extend (s-extend Θ) sr r-extend (r-extend ρ)) (s-extend (s-extend (Θ sr ρ)))
  extend-sr-twice Θ ρ = ap s-extend (extend-sr-once Θ ρ) ∘ extend-sr-once (s-extend Θ) (r-extend ρ)

  sr-comp : ∀ {Γ Γ' Γ'' τ} → (Θ : sctx Γ Γ') → (ρ : rctx Γ' Γ'') → (e : Γ'' |- τ)
          → (subst (ren e ρ) Θ) == subst e (Θ sr ρ)
  sr-comp Θ ρ unit = Refl
  sr-comp Θ ρ 0C = Refl
  sr-comp Θ ρ 1C = Refl
  sr-comp Θ ρ (plusC e e₁) = ap2 plusC (sr-comp Θ ρ e) (sr-comp Θ ρ e₁)
  sr-comp Θ ρ (var x) = svar-sr Θ ρ x
  sr-comp Θ ρ z = Refl
  sr-comp Θ ρ (suc e) = ap suc (sr-comp Θ ρ e)
  sr-comp Θ ρ (rec e e₁ e₂) = ap3 rec (sr-comp Θ ρ e) (sr-comp Θ ρ e₁)
                                      (ap (subst e₂) (ap s-extend (extend-sr-once Θ ρ) ∘
                                      extend-sr-once (s-extend Θ) (r-extend ρ)) ∘
                                      sr-comp (s-extend (s-extend Θ)) (r-extend (r-extend ρ)) e₂)
  sr-comp Θ ρ (lam e) = ap lam (ap (subst e) (extend-sr-once Θ ρ) ∘ sr-comp (s-extend Θ) (r-extend ρ) e)
  sr-comp Θ ρ (app e e₁) = ap2 app (sr-comp Θ ρ e) (sr-comp Θ ρ e₁)
  sr-comp Θ ρ (prod e e₁) = ap2 prod (sr-comp Θ ρ e) (sr-comp Θ ρ e₁)
  sr-comp Θ ρ (l-proj e) = ap l-proj (sr-comp Θ ρ e)
  sr-comp Θ ρ (r-proj e) = ap r-proj (sr-comp Θ ρ e)
  sr-comp Θ ρ nil = Refl
  sr-comp Θ ρ (e ::c e₁) = ap2 _::c_ (sr-comp Θ ρ e) (sr-comp Θ ρ e₁)
  sr-comp Θ ρ (listrec e e₁ e₂) = ap3 listrec (sr-comp Θ ρ e) (sr-comp Θ ρ e₁)
                                              (ap (subst e₂) (ap s-extend (ap s-extend (extend-sr-once Θ ρ)) ∘
                                              extend-sr-twice (s-extend Θ) (r-extend ρ)) ∘
                                                 sr-comp (s-extend (s-extend (s-extend Θ)))
                                                 (r-extend (r-extend (r-extend ρ))) e₂)
                                              
  sr-comp Θ ρ true = Refl
  sr-comp Θ ρ false = Refl

  extend-ss-once-lemma : ∀ {A B C τ τ'} → (Θ1 : sctx A B) (Θ2 : sctx B C) (x : τ ∈ τ' :: C)
                       → _==_ {_} {τ' :: A |- τ} (s-extend (_ss_ Θ1 Θ2) x) (_ss_ (s-extend Θ1) (s-extend Θ2) x)
  extend-ss-once-lemma Θ1 Θ2 i0 = Refl
  extend-ss-once-lemma Θ1 Θ2 (iS x) = ! (sr-comp (s-extend Θ1) iS (Θ2 x)) ∘ rs-comp iS Θ1 (Θ2 x)

  extend-ss-once : ∀ {A B C τ} → (Θ1 : sctx A B) (Θ2 : sctx B C)
              → _==_ {_} {sctx (τ :: A) (τ :: C)} (s-extend (Θ1 ss Θ2))
              ((s-extend Θ1) ss
              (s-extend Θ2))
  extend-ss-once Θ1 Θ2 = λ=i (λ τ → λ= (λ x → extend-ss-once-lemma Θ1 Θ2 x))

  subst-ss : ∀ {A B C τ} → (Θ1 : sctx A B) (Θ2 : sctx B C) (e : C |- τ)
           → subst e (Θ1 ss Θ2) == subst (subst e Θ2) Θ1
  subst-ss Θ1 Θ2 unit = Refl
  subst-ss Θ1 Θ2 0C = Refl
  subst-ss Θ1 Θ2 1C = Refl
  subst-ss Θ1 Θ2 (plusC e e₁) = ap2 plusC (subst-ss Θ1 Θ2 e) (subst-ss Θ1 Θ2 e₁)
  subst-ss Θ1 Θ2 (var x) = svar-ss Θ1 Θ2 x
  subst-ss Θ1 Θ2 z = Refl
  subst-ss Θ1 Θ2 (suc e) = ap suc (subst-ss Θ1 Θ2 e)
  subst-ss Θ1 Θ2 (rec e e₁ e₂) = ap3 rec (subst-ss Θ1 Θ2 e) (subst-ss Θ1 Θ2 e₁)
                                 (subst-ss (s-extend (s-extend Θ1)) (s-extend (s-extend Θ2)) e₂ ∘
                                 ap (subst e₂) (extend-ss-once (s-extend Θ1) (s-extend Θ2) ∘
                                 ap s-extend (extend-ss-once Θ1 Θ2)))
  subst-ss Θ1 Θ2 (lam e) = ap lam (subst-ss (s-extend Θ1) (s-extend Θ2) e ∘ ap (subst e) (extend-ss-once Θ1 Θ2))
  subst-ss Θ1 Θ2 (app e e₁) = ap2 app (subst-ss Θ1 Θ2 e) (subst-ss Θ1 Θ2 e₁)
  subst-ss Θ1 Θ2 (prod e e₁) = ap2 prod (subst-ss Θ1 Θ2 e) (subst-ss Θ1 Θ2 e₁)
  subst-ss Θ1 Θ2 (l-proj e) = ap l-proj (subst-ss Θ1 Θ2 e)
  subst-ss Θ1 Θ2 (r-proj e) = ap r-proj (subst-ss Θ1 Θ2 e)
  subst-ss Θ1 Θ2 nil = Refl
  subst-ss Θ1 Θ2 (e ::c e₁) = ap2 _::c_ (subst-ss Θ1 Θ2 e) (subst-ss Θ1 Θ2 e₁)
  subst-ss Θ1 Θ2 true = Refl
  subst-ss Θ1 Θ2 false = Refl
  subst-ss Θ1 Θ2 (listrec e e₁ e₂) = ap3 listrec (subst-ss Θ1 Θ2 e) (subst-ss Θ1 Θ2 e₁)
                                     (subst-ss (s-extend (s-extend (s-extend Θ1))) (s-extend (s-extend (s-extend Θ2))) e₂ ∘
                                     ap (subst e₂) (extend-ss-once (s-extend (s-extend Θ1)) (s-extend (s-extend Θ2)) ∘
                                     ap s-extend (extend-ss-once (s-extend Θ1) (s-extend Θ2) ∘
                                     ap s-extend (extend-ss-once Θ1 Θ2))))

  throw : ∀ {Γ Γ' τ} → sctx Γ (τ :: Γ') → sctx Γ Γ'
  throw Θ x = Θ (iS x)

  fuse1 : ∀ {Γ Γ' τ τ'} (v : Γ |- τ') (Θ : sctx Γ Γ') (x : τ ∈ Γ') → (q v ss q∙ Θ) x == Θ x
  fuse1 v Θ x = subst (ren (Θ x) iS) (q v) =⟨ sr-comp (q v) iS (Θ x) ⟩
                subst (Θ x) (q v sr iS) =⟨ Refl ⟩
                subst (Θ x) ids =⟨ ! (subst-id (Θ x)) ⟩
                (Θ x ∎)

  subst-compose-lemma-lemma : ∀ {Γ Γ' τ τ'} (v : Γ |- τ') (Θ : sctx Γ Γ') (x : τ ∈ τ' :: Γ')
                            → _==_ {_} {Γ |- τ} (_ss_ (q v) (s-extend Θ) x) (lem3' Θ v x)
  subst-compose-lemma-lemma v Θ i0 = Refl
  subst-compose-lemma-lemma v Θ (iS x) = fuse1 v Θ x

  subst-compose-lemma : ∀ {Γ Γ' τ} (v : Γ |- τ) (Θ : sctx Γ Γ')
                      → _==_ {_} {sctx Γ (τ :: Γ')} ((q v) ss (s-extend Θ)) (lem3' Θ v)
  subst-compose-lemma v Θ = λ=i (λ τ → λ= (λ x → subst-compose-lemma-lemma v Θ x))

  subst-compose : ∀ {Γ Γ' τ τ1} (Θ : sctx Γ Γ') (v : Γ |- τ) (e : (τ :: Γ' |- τ1) )
                → subst (subst e (s-extend Θ)) (q v) == subst e (lem3' Θ v)
  subst-compose Θ v e = ap (subst e) (subst-compose-lemma v Θ) ∘ (! (subst-ss (q v) (s-extend Θ) e))

  fuse2 : ∀ {Γ Γ' τ τ1 τ2} (v1 : Γ |- τ1) (v2 : Γ |- τ2) (Θ : sctx Γ Γ') (x : τ ∈ τ2 :: Γ')
        → (lem4 v1 v2 ss throw (s-extend (s-extend Θ))) x == (lem3' Θ v2) x
  fuse2 v1 v2 Θ x = subst (ren (s-extend Θ x) iS) (lem4 v1 v2) =⟨ sr-comp (lem4 v1 v2) iS (s-extend Θ x) ⟩
                    subst (s-extend Θ x) (lem4 v1 v2 sr iS) =⟨ Refl ⟩
                    subst (s-extend Θ x) (lem3' ids v2) =⟨ subst-compose-lemma-lemma v2 Θ x ⟩
                    (lem3' Θ v2 x ∎)

  subst-compose2-lemma-lemma : ∀ {Γ Γ' τ τ1 τ2 τ'} (v1 : Γ |- τ1) (v2 : Γ |- τ2) (e1 : τ1 :: τ2 :: Γ' |- τ) (Θ : sctx Γ Γ') (x : τ' ∈ τ1 :: τ2 :: Γ')
                             → _==_ {_} {_} ((lem4 v1 v2 ss s-extend (s-extend Θ)) x) (lem4' Θ v1 v2 x)
  subst-compose2-lemma-lemma v1 v2 e1 Θ i0 = Refl
  subst-compose2-lemma-lemma v1 v2 e1 Θ (iS x) = fuse2 v1 v2 Θ x

  subst-compose2-lemma : ∀ {Γ Γ' τ τ1 τ2} (v1 : Γ |- τ1) (v2 : Γ |- τ2) (e1 : τ1 :: τ2 :: Γ' |- τ) (Θ : sctx Γ Γ')
                       → _==_ {_} {sctx Γ (τ1 :: τ2 :: Γ')} (lem4 v1 v2 ss s-extend (s-extend Θ)) (lem4' Θ v1 v2)
  subst-compose2-lemma v1 v2 e1 Θ = λ=i (λ τ → λ= (λ x → subst-compose2-lemma-lemma v1 v2 e1 Θ x))

  postulate
    fuse3 : ∀ {Γ Γ' τ1 τ2 τ'} (Θ : sctx Γ Γ') (v1 : Γ' |- τ1) (v2 : Γ' |- τ2) (x : τ' ∈ τ2 :: Γ')
          → subst (lem3' ids v2 x) Θ == lem3' Θ (subst v2 Θ) x
  {-fuse3 Θ v1 v2 x = (Θ ss lem3' ids v2) x =⟨ Refl ⟩
                    (Θ ss q v2) x =⟨ {!!} ⟩
                    {!!} =⟨ {!!} ⟩
                    (q (subst v2 Θ) ss s-extend Θ) x =⟨ subst-compose-lemma-lemma (subst v2 Θ) Θ x ⟩
                    (lem3' Θ (subst v2 Θ) x ∎)
                    -- subst (lem3' ids v2 x) Θ =⟨ {!!} ⟩ --fuse2 (subst v1 Θ) (subst v2 Θ) Θ x ⟩ --subst-ss ids (lem3' Θ (subst v2 Θ)) {!var x!} ⟩
                    --(lem4 (subst v1 Θ) (subst v2 Θ) ss throw (s-extend (s-extend Θ))) x =⟨ fuse2 (subst v1 Θ) (subst v2 Θ) Θ x ⟩
                    --(lem3' Θ (subst v2 Θ) x ∎)-}

  subst-compose3-lemma-lemma : ∀ {Γ Γ' τ τ1 τ2 τ'} (Θ : sctx Γ Γ') (e1 : (τ1 :: (τ2 :: Γ')) |- τ) (v1 : Γ' |- τ1) (v2 : Γ' |- τ2) (x : τ' ∈ τ1 :: τ2 :: Γ')
                             → _==_ {_} {_} ((Θ ss lem4 v1 v2) x) (lem4' Θ (subst v1 Θ) (subst v2 Θ) x)
  subst-compose3-lemma-lemma Θ e1 v1 v2 i0 = Refl
  subst-compose3-lemma-lemma Θ e1 v1 v2 (iS x) = fuse3 Θ v1 v2 x

  subst-compose3-lemma : ∀ {Γ Γ' τ τ1 τ2} (Θ : sctx Γ Γ') (e1 : (τ1 :: (τ2 :: Γ')) |- τ) (v1 : Γ' |- τ1) (v2 : Γ' |- τ2)
                      → _==_ {_} {sctx Γ (τ1 :: τ2 :: Γ')} (Θ ss lem4 v1 v2) (lem4' Θ (subst v1 Θ) (subst v2 Θ))
  subst-compose3-lemma Θ e1 v1 v2 = λ=i (λ τ → λ= (λ x → subst-compose3-lemma-lemma Θ e1 v1 v2 x))

  subst-compose2 : ∀ {Γ Γ' τ τ1 τ2} (Θ : sctx Γ Γ') (e1 : (τ1 :: (τ2 :: Γ')) |- τ) (v1 : Γ |- τ1) (v2 : Γ |- τ2)
                 → subst (subst e1 (s-extend (s-extend Θ))) (lem4 v1 v2) == subst e1 (lem4' Θ v1 v2)
  subst-compose2 Θ e1 v1 v2 = ap (subst e1) (subst-compose2-lemma v1 v2 e1 Θ) ∘
                           ! (subst-ss (lem4 v1 v2) (s-extend (s-extend Θ)) e1)
{-
  subst-compose2 : ∀ {Γ Γ' τ} (Θ : sctx Γ Γ') (n : Γ |- nat) (e1 : Γ' |- τ) (e2 : (nat :: (τ :: Γ')) |- τ)
                →  subst (subst e2 (s-extend (s-extend Θ))) (lem4 n ((rec n (subst e1 Θ) (subst e2 (s-extend (s-extend Θ)))))) ==
                   subst e2 (lem4' Θ n ((rec n (subst e1 Θ) (subst e2 (s-extend (s-extend Θ))))))
  subst-compose2 Θ n e1 e2 = ap (subst e2) (subst-compose2-lemma n ((rec n (subst e1 Θ) (subst e2 (s-extend (s-extend Θ))))) e2 Θ) ∘
                             ! (subst-ss (lem4 n ((rec n (subst e1 Θ) (subst e2 (s-extend (s-extend Θ)))))) (s-extend (s-extend Θ)) e2)
-}
  subst-compose3 : ∀ {Γ Γ' τ τ1 τ2} (Θ : sctx Γ Γ') (e1 : (τ1 :: (τ2 :: Γ')) |- τ) (v1 : Γ' |- τ1) (v2 : Γ' |- τ2)
                 → subst (subst e1 (lem4 v1 v2)) Θ == subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ))
  subst-compose3 Θ e1 v1 v2 = ap (subst e1) (subst-compose3-lemma Θ e1 v1 v2) ∘ ! (subst-ss Θ (lem4 v1 v2) e1)

  subst-compose4 : ∀ {Γ Γ' τ} (Θ : sctx Γ Γ') (v' : Γ |- nat) (r : Γ |- τ) (e2 : (nat :: (τ :: Γ')) |- τ)
                 → subst (subst e2 (s-extend (s-extend Θ))) (lem4 v' r) == subst e2 (lem4' Θ v' r)
  subst-compose4 Θ v' r e2 = subst-compose2 Θ e2 v' r

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
          → subst e (q e2) ≤s app (lam e) e2
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
                → subst e1 (lem4 e (rec e e0 e1)) ≤s (rec (suc e) e0 e1)
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
  [ list A ]t = Nat , nat-p
  [ bool ]t = unit-p
  [ C ]t = Nat , nat-p
  
  -- interpret contexts as preorders
  [_]c : Ctx → PREORDER
  [ [] ]c = unit-p
  [ τ :: Γ ]c = [ τ ]t ×p [ Γ ]c

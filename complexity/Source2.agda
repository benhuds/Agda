{- Name: Bowornmet (Ben) Hudson

-- new source language module. trying stuff out

-}

open import Preliminaries
open import Preorder-withmax

module Source2 where

  data Tp : Set where
    unit : Tp
    nat : Tp
    susp : Tp → Tp
    _->s_ : Tp → Tp → Tp
    _×s_ : Tp → Tp → Tp
    list : Tp → Tp
    bool : Tp

  Ctx = List Tp

  -- de Bruijn indices
  data _∈_ : Tp → Ctx → Set where
    i0 : ∀ {Γ τ} → τ ∈ τ :: Γ
    iS : ∀ {Γ τ τ1} → τ ∈ Γ → τ ∈ τ1 :: Γ

  data _|-_ : Ctx → Tp → Set where
    unit : ∀ {Γ} → Γ |- unit
    var : ∀ {Γ τ}
        → τ ∈ Γ
        → Γ |- τ
    z : ∀ {Γ} → Γ |- nat
    suc : ∀ {Γ}
        → (e : Γ |- nat)
        → Γ |- nat
    rec : ∀ {Γ τ} → Γ |- nat → Γ |- τ → (nat :: (susp τ :: Γ)) |- τ
        → Γ |- τ
    lam : ∀ {Γ τ ρ} → (ρ :: Γ) |- τ
        → Γ |- (ρ ->s τ)
    app : ∀ {Γ τ1 τ2}
        → Γ |- (τ2 ->s τ1) → Γ |- τ2
        → Γ |- τ1
    prod : ∀ {Γ τ1 τ2}
         → Γ |- τ1 → Γ |- τ2
         → Γ |- (τ1 ×s τ2)
    delay : ∀ {Γ τ}
          → Γ |- τ
          → Γ |- susp τ
    force : ∀ {Γ τ}
          → Γ |- susp τ
          → Γ |- τ
    split : ∀ {Γ τ τ1 τ2}
          → Γ |- (τ1 ×s τ2) → (τ1 :: (τ2 :: Γ)) |- τ
          → Γ |- τ
    nil : ∀ {Γ τ} → Γ |- list τ
    _::s_ : ∀ {Γ τ} → Γ |- τ → Γ |- list τ → Γ |- list τ
    listrec : ∀ {Γ τ τ'} → Γ |- list τ → Γ |- τ' → (τ :: (list τ :: (susp τ' :: Γ))) |- τ' → Γ |- τ'
    true : ∀ {Γ} → Γ |- bool
    false : ∀ {Γ} → Γ |- bool

  module RenSubst where

      -- renaming = variable for variable substitution
      --functional view:
      --avoids induction,
      --some associativity/unit properties for free
    module Ren where

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
      ren (var x) ρ = var (ρ x)
      ren z ρ = z
      ren (suc e) ρ = suc (ren e ρ)
      ren (rec e e₁ e₂) ρ = rec (ren e ρ) (ren e₁ ρ) (ren e₂ (r-extend (r-extend ρ)))
      ren (lam e) ρ = lam (ren e (r-extend ρ))
      ren (app e e₁) ρ = app (ren e ρ) (ren e₁ ρ)
      ren (prod e1 e2) ρ = prod (ren e1 ρ) (ren e2 ρ)
      ren (delay e) ρ = delay (ren e ρ)
      ren (force e) ρ = force (ren e ρ)
      ren (split e e₁) ρ = split (ren e ρ) (ren e₁ (r-extend (r-extend ρ)))
      -- list stuff
      ren nil ρ = nil
      ren (x ::s xs) ρ = ren x ρ ::s ren xs ρ
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
      ren-comp ρ1 ρ2 (delay e) = ap delay (ren-comp ρ1 ρ2 e)
      ren-comp ρ1 ρ2 (force e) = ap force (ren-comp ρ1 ρ2 e)
      ren-comp ρ1 ρ2 (split e e₁) = ap2 split (ren-comp ρ1 ρ2 e)
                                        (ap (ren e₁) (ap r-extend (extend-ren-comp ρ1 ρ2) ∘
                                        extend-ren-comp (r-extend ρ1) (r-extend ρ2)) ∘
                                        ren-comp (r-extend (r-extend ρ1)) (r-extend (r-extend ρ2)) e₁)
      ren-comp ρ1 ρ2 nil = Refl
      ren-comp ρ1 ρ2 (e ::s e₁) = ap2 _::s_ (ren-comp ρ1 ρ2 e) (ren-comp ρ1 ρ2 e₁)
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

    open Ren

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
    q e  = lem3' ids e

    -- subst-var
    svar : ∀ {Γ1 Γ2 τ} → sctx Γ1 Γ2 → τ ∈ Γ2 → Γ1 |- τ
    svar Θ i = q (Θ i) i0

    lem4' : ∀ {Γ Γ' τ1 τ2} → sctx Γ Γ' → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ'))
    lem4' Θ a b = lem3' (lem3' Θ b) a

    lem4 : ∀ {Γ τ1 τ2} → Γ |- τ1 → Γ |- τ2 → sctx Γ (τ1 :: (τ2 :: Γ))
    lem4 e1 e2 = lem4' ids e1 e2

    subst : ∀ {Γ Γ' τ} → Γ' |- τ → sctx Γ Γ' → Γ |- τ
    subst unit Θ = unit
    subst (var x) Θ = Θ x
    subst z Θ = z
    subst (suc e) Θ = suc (subst e Θ)
    subst (rec e e₁ e₂) Θ = rec (subst e Θ) (subst e₁ Θ) (subst e₂ (s-extend (s-extend Θ)))
    subst (lam e) Θ = lam (subst e (s-extend Θ))
    subst (app e e₁) Θ = app (subst e Θ) (subst e₁ Θ)
    subst (prod e1 e2) Θ = prod (subst e1 Θ) (subst e2 Θ)
    subst (delay e) Θ = delay (subst e Θ)
    subst (force e) Θ = force (subst e Θ)
    subst (split e e₁) Θ = split (subst e Θ) (subst e₁ (s-extend (s-extend Θ)))
      -- list stuff
    subst nil Θ = nil
    subst (x ::s xs) Θ = subst x Θ ::s subst xs Θ
    subst true Θ = true
    subst false Θ = false
    subst (listrec e e₁ e₂) Θ = listrec (subst e Θ) (subst e₁ Θ) (subst e₂ (s-extend (s-extend (s-extend Θ))))

    subst1 : ∀ {τ τ1} → [] |- τ1 → (τ1 :: []) |- τ → [] |- τ
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
    subst-id (var x) = svar-id x
    subst-id z = Refl
    subst-id (suc e) = ap suc (subst-id e)
    subst-id (rec e e₁ e₂) = ap3 rec (subst-id e) (subst-id e₁) (ap (subst e₂) extend-id-twice ∘ subst-id e₂)
    subst-id (lam e) = ap lam (ap (subst e) extend-id-once ∘ subst-id e)
    subst-id (app e e₁) = ap2 app (subst-id e) (subst-id e₁)
    subst-id (prod e e₁) = ap2 prod (subst-id e) (subst-id e₁)
    subst-id (delay e) = ap delay (subst-id e)
    subst-id (force e) = ap force (subst-id e)
    subst-id (split e e₁) = ap2 split (subst-id e) (ap (subst e₁) extend-id-twice ∘ subst-id e₁)
    subst-id nil = Refl
    subst-id (e ::s e₁) = ap2 _::s_ (subst-id e) (subst-id e₁)
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
    subst-rs ρ Θ (var x) = svar-rs ρ Θ x
    subst-rs ρ Θ z = Refl
    subst-rs ρ Θ (suc e) = ap suc (subst-rs ρ Θ e)
    subst-rs ρ Θ (rec e e₁ e₂) = ap3 rec (subst-rs ρ Θ e) (subst-rs ρ Θ e₁)
                                   (ap (subst e₂) (extend-rs-twice ρ Θ) ∘
                                   subst-rs (r-extend (r-extend ρ)) (s-extend (s-extend Θ)) e₂)
    subst-rs ρ Θ (lam e) = ap lam (ap (subst e) (extend-rs-once ρ Θ) ∘ subst-rs (r-extend ρ) (s-extend Θ) e)
    subst-rs ρ Θ (app e e₁) = ap2 app (subst-rs ρ Θ e) (subst-rs ρ Θ e₁)
    subst-rs ρ Θ (prod e e₁) = ap2 prod (subst-rs ρ Θ e) (subst-rs ρ Θ e₁)
    subst-rs ρ Θ (delay e) = ap delay (subst-rs ρ Θ e)
    subst-rs ρ Θ (force e) = ap force (subst-rs ρ Θ e)
    subst-rs ρ Θ (split e e₁) = ap2 split (subst-rs ρ Θ e)
                                          (ap (subst e₁) (extend-rs-twice ρ Θ) ∘
                                          subst-rs (r-extend (r-extend ρ)) (s-extend (s-extend Θ)) e₁)
    subst-rs ρ Θ nil = Refl
    subst-rs ρ Θ (e ::s e₁) = ap2 _::s_ (subst-rs ρ Θ e) (subst-rs ρ Θ e₁)
    subst-rs ρ Θ true = Refl
    subst-rs ρ Θ false = Refl
    subst-rs ρ Θ (listrec e e₁ e₂) = ap3 listrec (subst-rs ρ Θ e) (subst-rs ρ Θ e₁)
                                         (ap (subst e₂) (ap s-extend (ap s-extend (extend-rs-once ρ Θ)) ∘
                                         extend-rs-twice (r-extend ρ) (s-extend Θ)) ∘
                                         subst-rs (r-extend (r-extend (r-extend ρ))) (s-extend (s-extend (s-extend Θ))) e₂)

    rs-comp : ∀ {Γ Γ' Γ'' τ} → (ρ : rctx Γ Γ') → (Θ : sctx Γ' Γ'') → (e : Γ'' |- τ)
            → (ren (subst e Θ) ρ) == subst e (ρ rs Θ)
    rs-comp ρ Θ unit = Refl
    rs-comp ρ Θ (var x) = svar-rs ρ Θ x
    rs-comp ρ Θ z = Refl
    rs-comp ρ Θ (suc e) = ap suc (rs-comp ρ Θ e)
    rs-comp ρ Θ (rec e e₁ e₂) = ap3 rec (rs-comp ρ Θ e) (rs-comp ρ Θ e₁)
                                (ap (subst e₂) (extend-rs-twice ρ Θ) ∘ rs-comp (r-extend (r-extend ρ)) (s-extend (s-extend Θ)) e₂)
    rs-comp ρ Θ (lam e) = ap lam (ap (subst e) (extend-rs-once ρ Θ) ∘ rs-comp (r-extend ρ) (s-extend Θ) e)
    rs-comp ρ Θ (app e e₁) = ap2 app (rs-comp ρ Θ e) (rs-comp ρ Θ e₁)
    rs-comp ρ Θ (prod e e₁) = ap2 prod (rs-comp ρ Θ e) (rs-comp ρ Θ e₁)
    rs-comp ρ Θ (delay e) = ap delay (rs-comp ρ Θ e)
    rs-comp ρ Θ (force e) = ap force (rs-comp ρ Θ e)
    rs-comp ρ Θ (split e e₁) = ap2 split (rs-comp ρ Θ e) (ap (subst e₁) (extend-rs-twice ρ Θ) ∘ rs-comp (r-extend (r-extend ρ)) (s-extend (s-extend Θ)) e₁)
    rs-comp ρ Θ nil = Refl
    rs-comp ρ Θ (e ::s e₁) = ap2 _::s_ (rs-comp ρ Θ e) (rs-comp ρ Θ e₁)
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
    sr-comp Θ ρ (delay e) = ap delay (sr-comp Θ ρ e)
    sr-comp Θ ρ (force e) = ap force (sr-comp Θ ρ e)
    sr-comp Θ ρ (split e e₁) = ap2 split (sr-comp Θ ρ e) (ap (subst e₁) (ap s-extend (extend-sr-once Θ ρ) ∘
                                                         extend-sr-once (s-extend Θ) (r-extend ρ)) ∘
                                                         sr-comp (s-extend (s-extend Θ)) (r-extend (r-extend ρ)) e₁)
    sr-comp Θ ρ nil = Refl
    sr-comp Θ ρ (e ::s e₁) = ap2 _::s_ (sr-comp Θ ρ e) (sr-comp Θ ρ e₁)
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
    subst-ss Θ1 Θ2 (delay e) = ap delay (subst-ss Θ1 Θ2 e)
    subst-ss Θ1 Θ2 (force e) = ap force (subst-ss Θ1 Θ2 e)
    subst-ss Θ1 Θ2 (split e e₁) = ap2 split (subst-ss Θ1 Θ2 e)
                                            (subst-ss (s-extend (s-extend Θ1)) (s-extend (s-extend Θ2)) e₁ ∘
                                            ap (subst e₁) (extend-ss-once (s-extend Θ1) (s-extend Θ2) ∘
                                            ap s-extend (extend-ss-once Θ1 Θ2)))
    subst-ss Θ1 Θ2 nil = Refl
    subst-ss Θ1 Θ2 (e ::s e₁) = ap2 _::s_ (subst-ss Θ1 Θ2 e) (subst-ss Θ1 Θ2 e₁)
    subst-ss Θ1 Θ2 true = Refl
    subst-ss Θ1 Θ2 false = Refl
    subst-ss Θ1 Θ2 (listrec e e₁ e₂) = ap3 listrec (subst-ss Θ1 Θ2 e) (subst-ss Θ1 Θ2 e₁)
                                       (subst-ss (s-extend (s-extend (s-extend Θ1))) (s-extend (s-extend (s-extend Θ2))) e₂ ∘
                                       ap (subst e₂) (extend-ss-once (s-extend (s-extend Θ1)) (s-extend (s-extend Θ2)) ∘
                                       ap s-extend (extend-ss-once (s-extend Θ1) (s-extend Θ2) ∘
                                       ap s-extend (extend-ss-once Θ1 Θ2))))

    ss-comp : ∀ {Γ Γ' Γ'' τ} → (Θ1 : sctx Γ Γ') → (Θ2 : sctx Γ' Γ'') → (e : Γ'' |- τ)
            → (subst (subst e Θ2) Θ1) == subst e (Θ1 ss Θ2)
    ss-comp = {!!}

    subst-compose-lemma-lemma : ∀ {Γ Γ' τ τ'} (v : Γ |- τ') (Θ : sctx Γ Γ') (x : τ ∈ τ' :: Γ')
                              → _==_ {_} {Γ |- τ} (_ss_ (q v) (s-extend Θ) x) (lem3' Θ v x)
    subst-compose-lemma-lemma v Θ i0 = Refl
    subst-compose-lemma-lemma v Θ (iS x) = {!!}

    subst-compose-lemma : ∀ {Γ Γ' τ} (v : Γ |- τ) (Θ : sctx Γ Γ')
                        → _==_ {_} {sctx Γ (τ :: Γ')} ((q v) ss (s-extend Θ)) (lem3' Θ v)
    subst-compose-lemma v Θ = λ=i (λ τ → λ= (λ x → subst-compose-lemma-lemma v Θ x))

    subst-compose : ∀ {Γ Γ' τ τ1} (Θ : sctx Γ Γ') (v : Γ |- τ) (e : (τ :: Γ' |- τ1) )
                  → subst (subst e (s-extend Θ)) (q v) == subst e (lem3' Θ v)
    subst-compose Θ v e = ap (subst e) (subst-compose-lemma v Θ) ∘ (! (subst-ss (q v) (s-extend Θ) e))

{-these lemmas can be compressed into one general lemma for subst-compose with 2 s-extends...-}

    subst-compose2 : ∀ {Γ Γ' τ} (Θ : sctx Γ Γ') (n : Γ |- nat) (e1 : Γ' |- τ) (e2 : (nat :: (susp τ :: Γ')) |- τ)
                  →  subst (subst e2 (s-extend (s-extend Θ))) (lem4 n (delay (rec n (subst e1 Θ) (subst e2 (s-extend (s-extend Θ)))))) ==
                     subst e2 (lem4' Θ n (delay (rec n (subst e1 Θ) (subst e2 (s-extend (s-extend Θ))))))
    subst-compose2 Θ n e1 e2 = ap (subst e2) {!!} ∘ ! (subst-ss (lem4 n (delay (rec n (subst e1 Θ) (subst e2 (s-extend (s-extend Θ)))))) (s-extend (s-extend Θ)) e2)

    subst-compose3 : ∀ {Γ Γ' τ τ1 τ2} (Θ : sctx Γ Γ') (e1 : (τ1 :: (τ2 :: Γ')) |- τ) (v1 : Γ |- τ1) (v2 : Γ |- τ2)
                   → subst (subst e1 (s-extend (s-extend Θ))) (lem4 v1 v2) == subst e1 (lem4' Θ v1 v2)
    subst-compose3 Θ e1 v1 v2 = ap (subst e1) {!!} ∘ ! (subst-ss (lem4 v1 v2) (s-extend (s-extend Θ)) e1)

    subst-compose4 : ∀ {Γ Γ' τ} (Θ : sctx Γ Γ') (v' : Γ |- nat) (r : Γ |- susp τ) (e2 : (nat :: (susp τ :: Γ')) |- τ)
                   → subst (subst e2 (s-extend (s-extend Θ))) (lem4 v' r) == subst e2 (lem4' Θ v' r)
    subst-compose4 Θ v' r e2 = ap (subst e2) {!!} ∘ ! (subst-ss (lem4 v' r) (s-extend (s-extend Θ)) e2)
                                      --i want to use ap with something like
                                      --subst-compose-lemma v' Θ
                                      --here but i think i'm missing something.
--(ap lem3' (subst-compose-lemma v' Θ)) ∘ ?

  open RenSubst

  --closed values of the source language
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
    nil-isval : ∀ {τ} → val (nil {_} {τ})
    cons-isval : ∀ {τ} (x : [] |- τ) → (xs : [] |- list τ)
               → val x → val xs
               → val (x ::s xs)
    true-isval : val true
    false-isval : val false

  module Costs where

    data Cost : Set where
      0c : Cost
      1c : Cost
      _+c_ : Cost → Cost → Cost

    data Equals0c : Cost → Set where
      Eq0-0c : Equals0c 0c
      Eq0-+c : ∀ {c c'} → Equals0c c → Equals0c c' → Equals0c (c +c c')

  open Costs

  mutual
    -- define evals (e : source exp) (v : value) (c : nat)
    -- analogous to "e evaluates to v in c steps"
    -- figure 2 from ICFP paper
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
               → evals (subst e0' (q v1)) v n
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
                  → evals (subst e1 (lem4 v1 v2)) v n2
                  → evals (split e0 e1) v (n1 +c n2)
      nil-evals : ∀ {τ : Tp} → evals (nil {_} {τ}) (nil {_} {τ}) 0c
      cons-evals : ∀ {n1 n2}
                 → {τ : Tp} {x v : [] |- τ} {xs vs : [] |- list τ}
                 → evals x v n1
                 → evals xs vs n2
                 → evals (x ::s xs) (v ::s vs) (n1 +c n2)
      true-evals : evals true true 0c
      false-evals : evals false false 0c

    -- means evals (rec v e0 e1) v' n 
    -- but helpful to have a separate type for this
    data evals-rec-branch {τ : Tp} (e0 : [] |- τ) (e1 : (nat :: (susp τ :: [])) |- τ) : (e : [] |- nat) (v : [] |- τ) → Cost → Set where
         evals-rec-z : ∀ {v n} → evals e0 v n → evals-rec-branch e0 e1 z v n 
         evals-rec-s : ∀ {v v' n} → evals (subst e1 (lem4 v (delay (rec v e0 e1)))) v' n
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
  evals-val nil-evals = nil-isval
  evals-val (cons-evals D D₁) = cons-isval _ _ (evals-val D) (evals-val D₁)
  evals-val true-evals = true-isval
  evals-val false-evals = false-isval

  -- lemma 2 from ICFP paper
  val-evals-inversion : {τ : Tp} {v v' : [] |- τ} {n : Cost} → val v → evals v v' n → (v == v') × Equals0c n
  val-evals-inversion z-isval z-evals = Refl , Eq0-0c
  val-evals-inversion (suc-isval e ve) (s-evals D) = (ap suc (fst IH)) , snd IH where
    IH = val-evals-inversion ve D
  val-evals-inversion (pair-isval e1 e2 ve1 ve2) (pair-evals D D₁) = ap2 prod (fst IH1) (fst IH2) , Eq0-+c (snd IH1) (snd IH2) where
    IH1 = val-evals-inversion ve1 D
    IH2 = val-evals-inversion ve2 D₁
  val-evals-inversion (lam-isval e) lam-evals = Refl , Eq0-0c
  val-evals-inversion unit-isval unit-evals = Refl , Eq0-0c
  val-evals-inversion (delay-isval e) delay-evals = Refl , Eq0-0c
  val-evals-inversion nil-isval nil-evals = Refl , Eq0-0c
  val-evals-inversion (cons-isval x xs vx vxs) (cons-evals D D₁) = ap2 _::s_ (fst IH1) (fst IH2) , Eq0-+c (snd IH1) (snd IH2) where
    IH1 = val-evals-inversion vx D
    IH2 = val-evals-inversion vxs D₁
  val-evals-inversion true-isval true-evals = Refl , Eq0-0c
  val-evals-inversion false-isval false-evals = Refl , Eq0-0c

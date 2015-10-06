open import Preliminaries

{-strong normalization for STLC. adapted from OPLSS-}

module STLC where

  data Tp : Set where
    b : Tp -- uninterpreted base type
    _⇒_ : Tp → Tp → Tp

  Ctx = List Tp

  data _∈_ : Tp → List Tp → Set where
    i0 : ∀ {Γ τ} → τ ∈ (τ :: Γ)
    iS : ∀ {Γ τ τ1} → τ ∈ Γ → τ ∈ (τ1 :: Γ)

  infixr 10 _⇒_
  infixr 8 _|-_

  data _|-_ : Ctx → Tp → Set where
    c   : ∀ {Γ} → Γ |- b -- some constant of the base type
    v   : ∀ {Γ τ} 
        → τ ∈ Γ
        → Γ |- τ
    lam : ∀ {Γ τ1 τ2} → (τ1 :: Γ) |- τ2 → Γ |- τ1 ⇒ τ2
    app : ∀ {Γ τ1 τ2} → Γ |- τ1 ⇒ τ2 → Γ |- τ1 → Γ |- τ2

  module RenSubst where

    rctx : Ctx → Ctx → Set
    rctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → τ ∈ Γ

    r-extend : ∀ {Γ Γ' τ} → rctx Γ Γ' → rctx (τ :: Γ) (τ :: Γ')
    r-extend ρ i0 = i0
    r-extend ρ (iS i) = iS (ρ i)

    ren : ∀ {Γ Γ' τ} → Γ' |- τ → rctx Γ Γ' → Γ |- τ
    ren c ρ = c
    ren (v x) ρ = v (ρ x)
    ren (lam e) ρ = lam (ren e (r-extend ρ))
    ren (app e e₁) ρ = app (ren e ρ) (ren e₁ ρ)

    sctx : Ctx → Ctx → Set
    sctx Γ Γ' = ∀ {τ} → τ ∈ Γ' → Γ |- τ

    wkn : ∀ {Γ τ1 τ2} → Γ |- τ2 → (τ1 :: Γ) |- τ2
    wkn e = ren e iS

    s-extend : ∀ {Γ Γ' τ} → sctx Γ Γ' → sctx (τ :: Γ) (τ :: Γ')
    s-extend Θ i0 = v i0
    s-extend Θ (iS x) = wkn (Θ x)

    subst : ∀ {Γ Γ' τ} → Γ' |- τ → sctx Γ Γ' → Γ |- τ
    subst c Θ = c
    subst (v x) Θ = Θ x
    subst (lam e) Θ = lam (subst e (s-extend Θ))
    subst (app e e₁) Θ = app (subst e Θ) (subst e₁ Θ)

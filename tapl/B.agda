open import Preliminaries

{-TAPL Chapter 3-}

module B where

  data Tp : Set where
    bool : Tp
    
  Ctx = List Tp

  data _∈_ : Tp → Ctx → Set where
    i0 : ∀ {Γ τ} → τ ∈ (τ :: Γ)
    iS : ∀ {Γ τ τ1} → τ ∈ Γ → τ ∈ (τ1 :: Γ)

  data _|-_ : Ctx → Tp → Set where
    t  : ∀ {Γ} → Γ |- bool
    f  : ∀ {Γ} → Γ |- bool
    if_then_else : ∀ {Γ τ} → Γ |- bool → Γ |- τ → Γ |- τ → Γ |- τ

  data val : ∀ {τ} → [] |- τ → Set where
    t-isval : val t
    f-isval : val f
  
  data _>>_ : ∀ {τ} → [] |- τ → [] |- τ → Set where
    if-t : ∀ {τ}
         → (t2 t3 : [] |- τ)
         → if t then t2 else t3 >> t2
    if-f : ∀ {τ}
         → (t2 t3 : [] |- τ)
         → if f then t2 else t3 >> t3
    if : ∀ {τ}
       → (t1 t1' : [] |- bool) (t2 t3 : [] |- τ)
       → t1 >> t1'
       → if t1 then t2 else t3 >> if t1' then t2 else t3

  progress : ∀ {τ} (e : [] |- τ) → Either (val e) (Σ (λ e' → (e >> e')))
  progress t = Inl t-isval
  progress f = Inl f-isval
  progress (if_then_else e e₁ e₂) with progress e
  progress (if_then_else .t e₁ e₂) | Inl t-isval = Inr (e₁ , (if-t e₁ e₂))
  progress (if_then_else .f e₁ e₂) | Inl f-isval = Inr (e₂ , (if-f e₁ e₂))
  progress (if_then_else e e₁ e₂) | Inr (e' , d) = Inr ((if e' then e₁ else e₂) , (if e e' e₁ e₂ d))

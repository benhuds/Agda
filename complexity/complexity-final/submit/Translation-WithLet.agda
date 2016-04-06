{- NEW TRANSLATION: notation change to avoid exponential increase in term size during translation -}

open import Preliminaries
open import Source
open import Complexity

module Translation-WithLet where

  mutual
    ⟨⟨_⟩⟩ : Tp → Complexity.CTp
    ⟨⟨ unit ⟩⟩ = unit
    ⟨⟨ nat ⟩⟩ = nat
    ⟨⟨ susp A ⟩⟩ = || A ||
    ⟨⟨ A ->s B ⟩⟩ = ⟨⟨ A ⟩⟩ ->c || B ||
    ⟨⟨ A ×s B ⟩⟩ = ⟨⟨ A ⟩⟩ ×c ⟨⟨ B ⟩⟩
    ⟨⟨ list A ⟩⟩ = list ⟨⟨ A ⟩⟩
    ⟨⟨ bool ⟩⟩ = bool
  
    ||_|| : Tp → Complexity.CTp
    || τ || = C ×c ⟨⟨ τ ⟩⟩

  ⟨⟨_⟩⟩c : Source.Ctx → Complexity.Ctx
  ⟨⟨ [] ⟩⟩c = []
  ⟨⟨ x :: Γ ⟩⟩c = ⟨⟨ x ⟩⟩ :: ⟨⟨ Γ ⟩⟩c

  interp-Cost : ∀{Γ} → Cost → Γ Complexity.|- C
  interp-Cost 0c = 0C
  interp-Cost 1c = 1C
  interp-Cost (m +c n) = plusC (interp-Cost m) (interp-Cost n)

  lookup : ∀{Γ τ} → τ Source.∈ Γ → ⟨⟨ τ ⟩⟩ Complexity.∈ ⟨⟨ Γ ⟩⟩c
  lookup i0 = i0
  lookup (iS x) = iS (lookup x)
  
  throw-s : ∀ {Γ Γ' τ} → Complexity.sctx Γ (τ :: Γ') → Complexity.sctx Γ Γ'
  throw-s Θ x = Θ (iS x)

  _+C_ : ∀ {Γ τ} → Γ Complexity.|- C  → Γ Complexity.|- (C ×c τ)→ Γ Complexity.|- (C ×c τ)
  c +C e = letc (prod (l-proj (var i0)) (r-proj (var i0))) e

  -- translation from source expressions to complexity expressions
  ||_||e : ∀{Γ τ} → Γ Source.|- τ → ⟨⟨ Γ ⟩⟩c Complexity.|- || τ ||
  || unit ||e = prod 0C unit
  || var x ||e = prod 0C (var (lookup x))
  || z ||e = prod 0C z
  || suc e ||e = (letc (prod (l-proj (var i0)) (s (r-proj (var i0)))) || e ||e)
  || rec e e0 e1 ||e =
      letc (l-proj (var i0) +C rec (r-proj (var i0))
           (Complexity.wkn (1C +C || e0 ||e)) (Complexity.subst (1C +C || e1 ||e) (Complexity.s-extend (Complexity.s-extend (throw-s Complexity.ids))))) || e ||e
  || lam e ||e = prod 0C (lam || e ||e) 
  || app e1 e2 ||e = letc (letc (prod (plusC (plusC (l-proj (var (iS i0))) (l-proj (var i0))) (l-proj (app (r-proj (var (iS i0))) (r-proj (var i0)))))
                            (r-proj (app (r-proj (var (iS i0))) (r-proj (var i0))))) (Complexity.wkn || e2 ||e)) || e1 ||e
  || prod e1 e2 ||e = letc (letc (prod (plusC (l-proj (var (iS i0))) (l-proj (var i0))) (prod (r-proj (var (iS i0))) (r-proj (var i0)))) (Complexity.wkn || e2 ||e)) || e1 ||e
  || delay e ||e = prod 0C || e ||e
  || force e ||e = letc (prod (plusC (l-proj (var i0)) (l-proj (r-proj (var i0)))) (r-proj (r-proj (var i0)))) || e ||e
  || split e0 e1 ||e = letc (prod (plusC (Complexity.wkn (l-proj || e0 ||e)) (l-proj (var i0))) (r-proj (var i0))) E1
       where E1 = letc (Complexity.subst || e1 ||e (Complexity.lem4 (l-proj (r-proj (var i0))) (r-proj (r-proj (var i0))) Complexity.ss Complexity.s-extend (Complexity.s-extend (throw-s Complexity.ids)))) || e0 ||e
  || nil ||e = prod 0C nil
  || e ::s e₁ ||e = letc (letc (prod (plusC (l-proj (var (iS i0))) (l-proj (var i0))) (r-proj (var (iS i0)) ::c r-proj (var i0))) (Complexity.wkn || e₁ ||e)) || e ||e
  || listrec e e₁ e₂ ||e =
      letc (l-proj (var i0) +C listrec (r-proj (var i0))
        (Complexity.wkn (1C +C || e₁ ||e)) (Complexity.subst (1C +C || e₂ ||e) (Complexity.s-extend (Complexity.s-extend (Complexity.s-extend (throw-s Complexity.ids)))))) || e ||e
  || true ||e = prod 0C true
  || false ||e = prod 0C false

{-
  module Proofs where
    open NewTranslation renaming (||_||e to ||_||new)
    open import Translation renaming (||_||e to ||_||old)

    convert-type : Complexity-WithLet.CTp → Complexity.CTp
    convert-type unit = unit
    convert-type nat = nat
    convert-type (τ ->c τ₁) = convert-type τ ->c convert-type τ₁
    convert-type (τ ×c τ₁) = convert-type τ ×c convert-type τ₁
    convert-type (list τ) = list (convert-type τ)
    convert-type bool = bool
    convert-type C = C
    convert-type rnat = rnat
  
    convert-ctx : Complexity-WithLet.Ctx → Complexity.Ctx
    convert-ctx [] = []
    convert-ctx (x :: Γ) = convert-type x :: convert-ctx Γ

    convert-var : ∀ {Γ τ} → τ Complexity-WithLet.∈ Γ → convert-type τ Complexity.∈ convert-ctx Γ
    convert-var i0 = i0
    convert-var (iS x) = iS (convert-var x)
  
    convert-exp : ∀{Γ τ} → (e : Γ Complexity-WithLet.|- τ) → convert-ctx Γ Complexity.|- convert-type τ
    convert-exp unit = unit
    convert-exp 0C = 0C
    convert-exp 1C = 1C
    convert-exp (plusC e e₁) = plusC (convert-exp e) (convert-exp e₁)
    convert-exp (var x) = var (convert-var x)
    convert-exp z = z
    convert-exp (s e) = s (convert-exp e)
    convert-exp (rec e e₁ e₂) = rec (convert-exp e) (convert-exp e₁) (convert-exp e₂)
    convert-exp (lam e) = lam (convert-exp e)
    convert-exp (app e e₁) = app (convert-exp e) (convert-exp e₁)
    convert-exp (prod e e₁) = {!!}
    convert-exp (l-proj e) = {!!}
    convert-exp (r-proj e) = {!!}
    convert-exp nil = {!!}
    convert-exp (e ::c e₁) = {!!}
    convert-exp (listrec e e₁ e₂) = {!!}
    convert-exp true = true
    convert-exp false = false
    convert-exp (max x e e₁) = max {!!} {!!} {!!}
    convert-exp (letc e e₁) = app (lam (convert-exp e)) (convert-exp e₁)

    trans-eq : ∀{Γ τ} → (e : Γ Source.|- τ)
                      → (t1 : convert-exp ?) --((NewTranslation.⟨⟨ Γ ⟩⟩c) Complexity-WithLet.|- NewTranslation.|| τ ||))
                      → (t2 : Translation.⟨⟨ Γ ⟩⟩c Complexity.|- Translation.|| τ ||)
                      → {!convert-exp t1!} == t2
    trans-eq e = {!!}
-}

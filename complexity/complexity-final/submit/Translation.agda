{- NEW TRANSLATION STUFF: same thing but interpret source nat as ♭nat-}

open import Preliminaries
open import Source
open import Complexity

module Translation where

  mutual
    ⟨⟨_⟩⟩ : Tp → CTp
    ⟨⟨ unit ⟩⟩ = unit
    ⟨⟨ nat ⟩⟩ = nat
    ⟨⟨ susp A ⟩⟩ = || A ||
    ⟨⟨ A ->s B ⟩⟩ = ⟨⟨ A ⟩⟩ ->c || B ||
    ⟨⟨ A ×s B ⟩⟩ = ⟨⟨ A ⟩⟩ ×c ⟨⟨ B ⟩⟩
    ⟨⟨ list A ⟩⟩ = list ⟨⟨ A ⟩⟩
    ⟨⟨ bool ⟩⟩ = bool

    ||_|| : Tp → CTp
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

  _+C_ : ∀ {Γ τ} → Γ Complexity.|- C  → Γ Complexity.|- (C ×c τ)→ Γ Complexity.|- (C ×c τ)
  c +C e = prod (plusC c (l-proj e)) (r-proj e)

  -- translation from source expressions to complexity expressions
  ||_||e : ∀{Γ τ} → Γ Source.|- τ → ⟨⟨ Γ ⟩⟩c Complexity.|- || τ ||
  || unit ||e = prod 0C unit
  || var x ||e = prod 0C (var (lookup x))
  || z ||e = prod 0C z
  || suc e ||e = prod (l-proj (|| e ||e)) (s (r-proj (|| e ||e)))
  || rec e e0 e1 ||e = (l-proj (|| e ||e)) +C (rec (r-proj || e ||e) (1C +C || e0 ||e) (1C +C || e1 ||e)) 
  || lam e ||e = prod 0C (lam || e ||e) 
  || app e1 e2 ||e =
    prod (plusC (plusC (plusC 1C (l-proj || e1 ||e)) (l-proj || e2 ||e)) (l-proj (app (r-proj || e1 ||e) (r-proj || e2 ||e))))
    (r-proj (app (r-proj || e1 ||e) (r-proj || e2 ||e)))
  || prod e1 e2 ||e = prod (plusC (l-proj (|| e1 ||e)) (l-proj (|| e2 ||e))) (prod (r-proj (|| e1 ||e)) (r-proj (|| e2 ||e)))
  || delay e ||e = prod 0C (|| e ||e)
  || force e ||e = prod (plusC (l-proj (|| e ||e)) (l-proj (r-proj || e ||e))) (r-proj (r-proj (|| e ||e)))
  || split e0 e1 ||e = prod (plusC (l-proj (|| e0 ||e)) (l-proj E1)) (r-proj E1)
    where E1 = (Complexity.subst || e1 ||e (Complexity.lem4 (l-proj (r-proj || e0 ||e)) (r-proj (r-proj || e0 ||e))))
  || nil ||e = prod 0C nil
  || e ::s e₁ ||e = prod (plusC (l-proj || e ||e) (l-proj || e₁ ||e)) ((r-proj || e ||e) ::c (r-proj || e₁ ||e))
  || listrec e e₁ e₂ ||e = l-proj || e ||e +C listrec (r-proj || e ||e) (1C +C || e₁ ||e) (1C +C || e₂ ||e)
  || true ||e = prod 0C true
  || false ||e = prod 0C false

  -- new translation with let bindings to reduce exponential increase in term size

  throw-s : ∀ {Γ Γ' τ} → Complexity.sctx Γ (τ :: Γ') → Complexity.sctx Γ Γ'
  throw-s Θ x = Θ (iS x)

  _+C'_ : ∀ {Γ τ} → Γ Complexity.|- C  → Γ Complexity.|- (C ×c τ)→ Γ Complexity.|- (C ×c τ)
  c +C' e = letc (prod (plusC (Complexity.wkn c) (l-proj (var i0))) (r-proj (var i0))) e

  ||_||e' : ∀{Γ τ} → Γ Source.|- τ → ⟨⟨ Γ ⟩⟩c Complexity.|- || τ ||
  || unit ||e' = prod 0C unit
  || var x ||e' = prod 0C (var (lookup x))
  || z ||e' = prod 0C z
  || suc e ||e' = (letc (prod (l-proj (var i0)) (s (r-proj (var i0)))) || e ||e')
--  || rec e e0 e1 ||e = (l-proj (|| e ||e)) +C (rec (r-proj || e ||e) (1C +C || e0 ||e) (1C +C || e1 ||e)) 
  || rec e e0 e1 ||e' =
      letc (l-proj (var i0) +C' rec (r-proj (var i0))
                   (Complexity.wkn (1C +C' || e0 ||e'))
                   (Complexity.subst (1C +C' || e1 ||e') (Complexity.s-extend (Complexity.s-extend (throw-s Complexity.ids)))))
           || e ||e'
  || lam e ||e' = prod 0C (lam || e ||e') 
  || app e1 e2 ||e' = letc (letc (prod (plusC (plusC (plusC 1C (l-proj (var (iS i0)))) (l-proj (var i0))) (l-proj (app (r-proj (var (iS i0))) (r-proj (var i0)))))
                            (r-proj (app (r-proj (var (iS i0))) (r-proj (var i0))))) (Complexity.wkn || e2 ||e')) || e1 ||e'
  || prod e1 e2 ||e' = letc (letc (prod (plusC (l-proj (var (iS i0))) (l-proj (var i0))) (prod (r-proj (var (iS i0))) (r-proj (var i0)))) (Complexity.wkn || e2 ||e')) || e1 ||e'
  || delay e ||e' = prod 0C || e ||e'
  || force e ||e' = letc (prod (plusC (l-proj (var i0)) (l-proj (r-proj (var i0)))) (r-proj (r-proj (var i0)))) || e ||e'
  || split e0 e1 ||e' = letc (prod (plusC (Complexity.wkn (l-proj || e0 ||e')) (l-proj (var i0))) (r-proj (var i0))) E1
       where E1 = letc (Complexity.subst || e1 ||e' (Complexity.lem4 (l-proj (r-proj (var i0))) (r-proj (r-proj (var i0))) Complexity.ss Complexity.s-extend (Complexity.s-extend (throw-s Complexity.ids)))) || e0 ||e'
  || nil ||e' = prod 0C nil
  || e ::s e₁ ||e' = letc (letc (prod (plusC (l-proj (var (iS i0))) (l-proj (var i0))) (r-proj (var (iS i0)) ::c r-proj (var i0))) (Complexity.wkn || e₁ ||e')) || e ||e'
  || listrec e e₁ e₂ ||e' =
      letc (l-proj (var i0) +C' listrec (r-proj (var i0))
        (Complexity.wkn (1C +C' || e₁ ||e')) (Complexity.subst (1C +C' || e₂ ||e') (Complexity.s-extend (Complexity.s-extend (Complexity.s-extend (throw-s Complexity.ids)))))) || e ||e'
  || true ||e' = prod 0C true
  || false ||e' = prod 0C false

{- try prove ||.||old <=/=> ||.||new
  
  trans-eq-l : ∀ {Γ τ} → (e : Γ Source.|- τ) → || e ||e ≤s || e ||e'
  trans-eq-l unit = refl-s
  trans-eq-l (var x) = refl-s
  trans-eq-l z = refl-s
  trans-eq-l (suc e) = (cong-prod (cong-lproj (trans-eq-l e)) (cong-suc (cong-rproj (trans-eq-l e))) trans lam-s) trans letc-app-r
  trans-eq-l (rec e e₁ e₂) = {!!}
  trans-eq-l (lam e) = cong-prod refl-s (cong-lam (trans-eq-l e))
  trans-eq-l (app e e₁) = {!!}
  trans-eq-l (prod e e₁) = (((cong-prod (cong-+ (cong-lproj {!!}) (cong-lproj {!!})) {!!} trans lam-s) trans letc-app-r) trans lam-s) trans letc-app-r
  trans-eq-l (delay e) = {!!}
  trans-eq-l (force e) = {!!}
  trans-eq-l (split e e₁) = {!!}
  trans-eq-l nil = {!!}
  trans-eq-l (e ::s e₁) = {!!}
  trans-eq-l (listrec e e₁ e₂) = {!!}
  trans-eq-l true = refl-s
  trans-eq-l false = refl-s
-}

{- NEW TRANSLATION STUFF: same thing but interpret source nat as ♭nat-}

open import Preliminaries
open import Source
open import Pilot2

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

  ⟨⟨_⟩⟩c : Source.Ctx → Pilot2.Ctx
  ⟨⟨ [] ⟩⟩c = []
  ⟨⟨ x :: Γ ⟩⟩c = ⟨⟨ x ⟩⟩ :: ⟨⟨ Γ ⟩⟩c

  interp-Cost : ∀{Γ} → Cost → Γ Pilot2.|- C
  interp-Cost 0c = 0C
  interp-Cost 1c = 1C
  interp-Cost (m +c n) = plusC (interp-Cost m) (interp-Cost n)

  lookup : ∀{Γ τ} → τ Source.∈ Γ → ⟨⟨ τ ⟩⟩ Pilot2.∈ ⟨⟨ Γ ⟩⟩c
  lookup i0 = i0
  lookup (iS x) = iS (lookup x)

  -- translation from source expressions to complexity expressions
  ||_||e : ∀{Γ τ} → Γ Source.|- τ → ⟨⟨ Γ ⟩⟩c Pilot2.|- || τ ||
  || unit ||e = prod 0C unit
  || var x ||e = prod 0C (var (lookup x))
  || z ||e = prod 0C z
  || suc e ||e = (letc (prod (l-proj (var i0)) (r-proj (var i0))) || e ||e)
  || rec e e0 e1 ||e =
      (letc (l-proj (var i0) +C rec (r-proj (var i0)) (Pilot2.wkn (1C +C || e0 ||e)) (Pilot2.wkn (1C +C {!|| e1 ||e!}))) || e ||e)
--((l-proj ?) +C (rec (r-proj ?) (1C +C || e0 ||e) (1C +C || e1 ||e)))
  || lam e ||e = prod 0C (lam || e ||e) 
  || app e1 e2 ||e = letc (letc (prod (plusC (plusC (l-proj (var (iS i0))) (l-proj (var i0))) (l-proj (app (r-proj (var (iS i0))) (r-proj (var i0)))))
                          (r-proj (app (r-proj (var (iS i0))) (r-proj (var i0))))) (Pilot2.wkn || e2 ||e)) || e1 ||e
  || prod e1 e2 ||e = letc (letc (prod (plusC (l-proj (var (iS i0))) (l-proj (var i0))) (prod (r-proj (var (iS i0))) (r-proj (var i0)))) (Pilot2.wkn || e2 ||e)) || e1 ||e
  || delay e ||e = prod 0C || e ||e
  || force e ||e = letc (prod (plusC (l-proj (var i0)) (l-proj (r-proj (var i0)))) (r-proj (r-proj (var i0)))) || e ||e
  || split e0 e1 ||e = letc (prod (plusC (Pilot2.wkn (l-proj || e0 ||e)) (l-proj (var i0))) (r-proj (var i0))) E1
    where E1 = letc (Pilot2.subst || e1 ||e {!!}) || e0 ||e
--(Pilot2.subst || e1 ||e (Pilot2.lem4 (l-proj (r-proj || e0 ||e)) (r-proj (r-proj || e0 ||e))))
  || nil ||e = prod 0C nil
  || e ::s e₁ ||e = letc (letc (prod (plusC (l-proj (var (iS i0))) (l-proj (var i0))) (r-proj (var (iS i0)) ::c r-proj (var i0))) (Pilot2.wkn || e₁ ||e)) || e ||e
  || listrec e e₁ e₂ ||e =
    let r = || e ||e in
    let r1 = || e₁ ||e in
    let r2 = || e₂ ||e in
      l-proj r +C listrec (r-proj r) (1C +C r1) (1C +C r2)
  || true ||e = prod 0C true
  || false ||e = prod 0C false

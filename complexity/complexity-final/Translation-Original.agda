{- NEW TRANSLATION STUFF: same thing but interpret source nat as ♭nat-}

open import Preliminaries
open import Source
open import Pilot2

module Translation-Original where

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
  || suc e ||e = prod (l-proj (|| e ||e)) (s (r-proj (|| e ||e)))
  || rec e e0 e1 ||e = (l-proj (|| e ||e)) +C (rec (r-proj || e ||e) (1C +C || e0 ||e) (1C +C || e1 ||e)) 
  || lam e ||e = prod 0C (lam || e ||e) 
  || app e1 e2 ||e =
    prod (plusC (plusC (plusC 1C (l-proj || e1 ||e)) (l-proj || e2 ||e)) (l-proj (app (r-proj || e1 ||e) (r-proj || e2 ||e))))
    (r-proj (app (r-proj || e1 ||e) (r-proj || e2 ||e)))
--prod (plusC (plusC (l-proj (|| e1 ||e)) (l-proj (|| e2 ||e))) (l-proj (app (r-proj (|| e1 ||e)) (r-proj (|| e2 ||e)))))
  --                        (r-proj (app (r-proj (|| e1 ||e)) (r-proj (|| e2 ||e))))
  || prod e1 e2 ||e = prod (plusC (l-proj (|| e1 ||e)) (l-proj (|| e2 ||e))) (prod (r-proj (|| e1 ||e)) (r-proj (|| e2 ||e)))
  || delay e ||e = prod 0C (|| e ||e)
  || force e ||e = prod (plusC (l-proj (|| e ||e)) (l-proj (r-proj || e ||e))) (r-proj (r-proj (|| e ||e)))
  || split e0 e1 ||e = prod (plusC (l-proj (|| e0 ||e)) (l-proj E1)) (r-proj E1)
    where E1 = (Pilot2.subst || e1 ||e (Pilot2.lem4 (l-proj (r-proj || e0 ||e)) (r-proj (r-proj || e0 ||e))))
  || nil ||e = prod 0C nil
  || e ::s e₁ ||e = prod (plusC (l-proj || e ||e) (l-proj || e₁ ||e)) ((r-proj || e ||e) ::c (r-proj || e₁ ||e))
  || listrec e e₁ e₂ ||e = l-proj || e ||e +C listrec (r-proj || e ||e) (1C +C || e₁ ||e) (1C +C || e₂ ||e)
  || true ||e = prod 0C true
  || false ||e = prod 0C false

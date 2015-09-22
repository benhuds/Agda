{-
  Translation from source types and expressions
  to complexity types and expressions
  *see page 9 of paper
-}

open import Preliminaries
open import Source2
open import Comp2

module Translation2 where

  -- translation from source types to complexity types
  mutual
    ⟨⟨_⟩⟩ : Tp → CTp
    ⟨⟨ unit ⟩⟩ = unit
    ⟨⟨ nat ⟩⟩ = nat
    ⟨⟨ susp A ⟩⟩ = || A ||
    ⟨⟨ A ->s B ⟩⟩ = ⟨⟨ A ⟩⟩ ->c || B ||
    ⟨⟨ A ×s B ⟩⟩ = ⟨⟨ A ⟩⟩ ×c ⟨⟨ B ⟩⟩

    ||_|| : Tp → CTp
    || τ || = C ×c ⟨⟨ τ ⟩⟩

  ⟨⟨_⟩⟩c : Source-lang.Ctx → Comp-lang.Ctx
  ⟨⟨ [] ⟩⟩c = []
  ⟨⟨ x :: Γ ⟩⟩c = ⟨⟨ x ⟩⟩ :: ⟨⟨ Γ ⟩⟩c

  -- translate source Cost types to complexity costs
  interp-Cost : ∀{Γ} → Cost → Γ Comp-lang.|- C
  interp-Cost 0c = 0C
  interp-Cost 1c = 1C
  interp-Cost (m +c n) = plusC (interp-Cost m) (interp-Cost n)

  -- need to fill this out
  postulate lookup : ∀{Γ τ} → τ Source-lang.∈ Γ → ⟨⟨ τ ⟩⟩ Comp-lang.∈ ⟨⟨ Γ ⟩⟩c

  -- translation from source expressions to complexity expressions
  ||_||e : ∀{Γ τ} → Γ Source-lang.|- τ → ⟨⟨ Γ ⟩⟩c Comp-lang.|- || τ ||
  || unit ||e = prod 0C unit
  || var x ||e = prod 0C (var (lookup x))
  || z ||e = prod 0C z
  || suc e ||e = prod (l-proj (|| e ||e)) (suc (r-proj (|| e ||e)))
  || rec e e0 e1 ||e = (l-proj (|| e ||e)) +C (rec (r-proj || e ||e) (1C +C || e0 ||e) (1C +C || e1 ||e)) 
  || lam e ||e = prod 0C (lam || e ||e) 
  || app e1 e2 ||e = prod (plusC (plusC (l-proj (|| e1 ||e)) (l-proj (|| e2 ||e))) (l-proj (app (r-proj (|| e1 ||e)) (r-proj (|| e2 ||e)))))
                          (r-proj (app (r-proj (|| e1 ||e)) (r-proj (|| e2 ||e))))
  || prod e1 e2 ||e = prod (plusC (l-proj (|| e1 ||e)) (l-proj (|| e2 ||e))) (prod (r-proj (|| e1 ||e)) (r-proj (|| e2 ||e)))
  || l-proj e ||e = prod (l-proj (|| e ||e)) (l-proj (r-proj (|| e ||e)))
  || r-proj e ||e = prod (l-proj (|| e ||e)) (r-proj (r-proj (|| e ||e)))
  || delay e ||e = prod 0C (|| e ||e)
  || force e ||e = prod (plusC (l-proj (|| e ||e)) (l-proj (r-proj || e ||e))) (r-proj (r-proj (|| e ||e)))

  || split e0 e1 ||e = prod (plusC (l-proj (|| e0 ||e)) (l-proj E1)) (r-proj E1)
    where E1 = (Comp-lang.subst (Comp-lang.lem4 (l-proj (r-proj || e0 ||e)) (r-proj (r-proj || e0 ||e))) || e1 ||e)

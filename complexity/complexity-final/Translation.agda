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
--    let r = || e ||e in
  --    prod (l-proj r) (s (r-proj r))
  || rec e e0 e1 ||e =
  --  let r = || e ||e in
      (letc (l-proj (var i0) +C rec (r-proj (var i0)) (Pilot2.wkn (1C +C || e0 ||e)) {!!}) || e ||e)
--((l-proj ?) +C (rec (r-proj ?) (1C +C || e0 ||e) (1C +C || e1 ||e)))
  || lam e ||e =
    let r = || e ||e in
      prod 0C (lam r) 
  || app e1 e2 ||e =
    let r1 = || e1 ||e in
    let r2 = || e2 ||e in
      prod (plusC (plusC (l-proj r1) (l-proj r2)) (l-proj (app (r-proj r1) (r-proj r2))))
                          (r-proj (app (r-proj r1) (r-proj r2)))
  || prod e1 e2 ||e =
    let r1 = || e1 ||e in
    let r2 = || e2 ||e in
      prod (plusC (l-proj r1) (l-proj r2)) (prod (r-proj r1) (r-proj r2))
  || delay e ||e =
    let r = || e ||e in
    prod 0C r
  || force e ||e =
    let r = || e ||e in
      prod (plusC (l-proj r) (l-proj (r-proj r))) (r-proj (r-proj r))
  || split e0 e1 ||e =
    let r0 = || e0 ||e in
      prod (plusC (l-proj r0) (l-proj E1)) (r-proj E1)
    where E1 = let r1 = || e1 ||e in let r0 = || e0 ||e in (Pilot2.subst r1 (Pilot2.lem4 (l-proj (r-proj r0)) (r-proj (r-proj r0))))
  || nil ||e = prod 0C nil
  || e ::s e₁ ||e =
    let r = || e ||e in
    let r1 = || e₁ ||e in
      prod (plusC (l-proj r) (l-proj r1)) ((r-proj r) ::c (r-proj r1))
  || listrec e e₁ e₂ ||e =
    let r = || e ||e in
    let r1 = || e₁ ||e in
    let r2 = || e₂ ||e in
      l-proj r +C listrec (r-proj r) (1C +C r1) (1C +C r2)
  || true ||e = prod 0C true
  || false ||e = prod 0C false

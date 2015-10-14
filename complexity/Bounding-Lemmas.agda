{-
  Lemmas for bounding theorem e.g. weakening of values 
-}

open import Preliminaries
open import Source-lang
open import Comp-lang
open import Translation

module Bounding_Lemmas where

  mutual
    valBound : ∀{τ} → (e : [] Source-lang.|- τ) → val e → [] Comp-lang.|- ⟨⟨ τ ⟩⟩ → Set
    valBound .z z-isval c = z ≤s c
    valBound .(suc n) (suc-isval n nv) c = Σ (λ c' → valBound n nv c' × suc c' ≤s c)
    valBound .(prod e1 e2) (pair-isval e1 e2 v1 v2) c = valBound e1 v1 (l-proj c) × valBound e2 v2 (r-proj c)
    valBound {τ1 ->s τ2} .(lam e) (lam-isval e) c = (v₁ : [] Source-lang.|- τ1) (vv : val v₁)
                                                    (c1 : [] Comp-lang.|- ⟨⟨ τ1 ⟩⟩) →
                                                    valBound v₁ vv c1 → expBound (Source-lang.subst (Source-lang.lem3 v₁) e) (app c c1)
    valBound .unit unit-isval c = Unit
    valBound .(delay _) (delay-isval e) c = expBound e c

    expBound : ∀{τ} → [] Source-lang.|- τ → [] Comp-lang.|- || τ || → Set
    expBound {τ} e b = (v₁ : [] Source-lang.|- τ) (vv : val v₁) (n : Cost) →
                         evals e v₁ n → interp-Cost n ≤s l-proj b × valBound v₁ vv (r-proj b)

  mutual
    weakeningExp : ∀{τ} → (e : [] Source-lang.|- τ) → (E E' : [] Comp-lang.|- || τ ||) → expBound e E → E ≤s E' → expBound e E'
    weakeningExp e c1 c2 d c1≤c2 e' ve' n i = trans-s (fst (d e' ve' n i)) (cong-lproj c1≤c2) , 
                                                      weakeningVal e' ve' (r-proj c1) (r-proj c2) (snd (d e' ve' n i)) (cong-rproj c1≤c2)

    weakeningVal : ∀{τ} → (v : [] Source-lang.|- τ) → (vv : val v) → (E E' : [] Comp-lang.|- ⟨⟨ τ ⟩⟩) → valBound v vv E → E ≤s E' → valBound v vv E'
    weakeningVal {unit} .unit unit-isval E E' vb e≤se' = <>
    weakeningVal {nat} .z z-isval E E' vb e≤se' = trans-s vb e≤se'
    weakeningVal {nat} .(suc e) (suc-isval e vv) E E' (i , iv , si≤se) e≤se' = i , iv , trans-s  si≤se e≤se'
    weakeningVal {susp τ} .(delay _) (delay-isval e) E E' vb e≤se' = weakeningExp e _ E' vb e≤se' --v₁ vv n x = ? --weakeningExp _ _ _ vb e≤se' v₁ vv n x
    weakeningVal {A ->s B} .(lam e) (lam-isval e) E E' vb e≤se' = 
      λ a va a' vba b b' n x → fst (vb a va a' vba b b' n x) trans cong-lproj (cong-app e≤se') , 
        weakeningVal b b' (r-proj (app E a')) (r-proj (app E' a')) (snd (vb a va a' vba b b' n x)) (cong-rproj (cong-app e≤se')) 
    weakeningVal {A ×s B} .(prod e1 e2) (pair-isval e1 e2 vv1 vv2) E E' vb e≤se' = weakeningVal e1 vv1 (l-proj E) (l-proj E') (fst vb) (cong-lproj e≤se') ,
                                                                                   weakeningVal e2 vv2 (r-proj E) (r-proj E') (snd vb) (cong-rproj e≤se')

  weakeningExp' : ∀{τ} {e : [] Source-lang.|- τ} {E E' : [] Comp-lang.|- || τ ||} → expBound e E → E ≤s E' → expBound e E'
  weakeningExp' eb e≤ = weakeningExp _ _ _ eb e≤

  weakeningVal' : ∀{τ} { v : [] Source-lang.|- τ} (vv : val v) {E E' : [] Comp-lang.|- ⟨⟨ τ ⟩⟩}
                → valBound v vv E → E ≤s E' → valBound v vv E'
  weakeningVal' vv v e = weakeningVal _ vv _ _ v e

  substVal : ∀{Γ} → (Θ : Source-lang.sctx [] Γ) → Set
  substVal {Γ} Θ = {τ : _} (x : τ Source-lang.∈ Γ) → val (Θ x)

  extend-substVal : ∀ {Γ' τ} {Θ : Source-lang.sctx [] Γ'} {e : [] Source-lang.|- τ}
                  → substVal Θ
                  → val e
                  → substVal (Source-lang.lem3' Θ e)
  extend-substVal sv vv i0 = vv
  extend-substVal sv vv (iS x) = sv x

-- {τ₁ : Tp} (x : τ₁ Source-lang.∈ ρ :: .Γ) → val (Source-lang.lem3' (λ {.τ} → Θ) v₁ x)

  extend-substVal2 : ∀ {Γ' τ1 τ2} {Θ : Source-lang.sctx [] Γ'} {e : [] Source-lang.|- τ1} {e' : [] Source-lang.|- τ2}
                   → substVal Θ
                   → val e → val e'
                   → substVal (Source-lang.lem4' Θ e e')
  extend-substVal2 sv vv vv' i0 = vv
  extend-substVal2 sv vv vv' (iS i0) = vv'
  extend-substVal2 sv vv vv' (iS (iS x)) = sv x

-- {τ₁ : Tp} (x : τ₁ Source-lang.∈ τ1 :: τ2 :: Γ) → val (lem4' (λ {.τ} → Θ) v1 v2 x)


  substBound : ∀{Γ} → (Θ : Source-lang.sctx [] Γ) → substVal Θ → (Θ' : Comp-lang.sctx [] ⟨⟨ Γ ⟩⟩c) → Set
  substBound {Γ} Θ vΘ Θ' = {τ : _} (x : τ Source-lang.∈ Γ) → valBound (Θ x) (vΘ x) (Θ' (lookup x))

  postulate
    extend-substBound : ∀{Γ τ} → {Θ : Source-lang.sctx [] Γ} {vΘ : substVal Θ} {Θ' : Comp-lang.sctx [] ⟨⟨ Γ ⟩⟩c}
                    → {e : [] Source-lang.|- τ} {ve : val e} {E : [] Comp-lang.|- ⟨⟨ τ ⟩⟩} 
                    → substBound Θ vΘ Θ'
                    → valBound e ve E
                    → substBound (Source-lang.lem3' Θ e) (extend-substVal vΘ ve) (Comp-lang.lem3' Θ' E)

  postulate
    extend-substBound2 : ∀{Γ τ1 τ2} → {Θ : Source-lang.sctx [] Γ} {vΘ : substVal Θ} {Θ' : Comp-lang.sctx [] ⟨⟨ Γ ⟩⟩c}
                       → {e : [] Source-lang.|- τ1} {ve : val e} {e' : [] Source-lang.|- τ2} {ve' : val e'}
                         {E : [] Comp-lang.|- ⟨⟨ τ1 ⟩⟩} {E' : [] Comp-lang.|- ⟨⟨ τ2 ⟩⟩}
                       → substBound Θ vΘ Θ'
                       → valBound e ve E → valBound e' ve' E'
                       → substBound (Source-lang.lem4' Θ e e') (extend-substVal2 vΘ ve ve') (Comp-lang.lem4' Θ' E E') --(Comp-lang.lem3' (Comp-lang.lem3' Θ' E') E)


  postulate
    inv : ∀ {τ} → (v v' : [] Source-lang.|- τ)
        → val v → val v' → (n : Cost) → evals v v' n → _≤s_{[]} (interp-Cost n) 0C

  --proved version of inversion lemma
  inv3 : ∀ {τ} {v v' : [] Source-lang.|- τ} {n : Cost} → val v → evals v v' n → _≤s_{[]} (interp-Cost n) 0C
  inv3 z-isval z-evals = refl-s
  inv3 (suc-isval e v) (s-evals evals) = inv3 v evals
  inv3 (pair-isval e1 e2 v v₁) (pair-evals evals evals₁) = cong-+ (inv3 v evals) (inv3 v₁ evals₁) trans +-unit-l trans refl-s
  inv3 (lam-isval e) lam-evals = refl-s
  inv3 unit-isval unit-evals = refl-s
  inv3 (delay-isval e) delay-evals = refl-s

  inv2 : ∀ {τ} {v e : [] Source-lang.|- τ} {n : Cost} -> val v → evals v e n → v == e
  inv2 z-isval z-evals = Refl
  inv2 (suc-isval e₁ val-v) (s-evals x) = ap suc (inv2 val-v x)
  inv2 (pair-isval e1 e2 val-v val-v₁) (pair-evals x x₁) = ap2 prod (inv2 val-v x) (inv2 val-v₁ x₁)
  inv2 (lam-isval e₁) lam-evals = Refl
  inv2 unit-isval unit-evals = Refl
  inv2 (delay-isval e₁) delay-evals = Refl

  val-hprop : ∀ {τ} {v : [] Source-lang.|- τ} → (d1 d2 : val v) → d1 == d2
  val-hprop z-isval z-isval = Refl
  val-hprop (suc-isval e d1) (suc-isval .e d2) = ap (suc-isval e) (val-hprop d1 d2)
  val-hprop (pair-isval e1 e2 d1 d2) (pair-isval .e1 .e2 d3 d4) = ap (λ x → pair-isval e1 e2 d3 x) (val-hprop d2 d4) ∘ ap (λ x → pair-isval e1 e2 x d2) (val-hprop d1 d3)
  val-hprop (lam-isval e) (lam-isval .e) = Refl
  val-hprop unit-isval unit-isval = Refl
  val-hprop (delay-isval e) (delay-isval .e) = Refl

  transport-valBound :  ∀{τ} {e e' : [] Source-lang.|- τ} {d : val e} {d' : val e'}
                     → (α : e == e')
                     → transport val α d == d'
                     → (E : [] Comp-lang.|- ⟨⟨ τ ⟩⟩)
                     → valBound e d E → valBound e' d' E
  transport-valBound Refl Refl E vb = vb

  Eq0C-≤0 : ∀ {n} → Equals0c n → _≤s_{[]} (interp-Cost n) 0C
  Eq0C-≤0 Eq0-0c = refl-s
  Eq0C-≤0 (Eq0-+c e e₁) = cong-+ (Eq0C-≤0 e) (Eq0C-≤0 e₁) trans +-unit-l


{- LEMMAS FOR BOUNDING THEOREM WITH NEW COMPLEXITY LANGUAGE -}

open import Preliminaries
open import Source
open import Pilot2
open import Translation-Original

module Bounding-Lemmas where

  mutual
    valBound : ∀{τ} → (e : [] Source.|- τ) → val e → [] Pilot2.|- ⟨⟨ τ ⟩⟩ → Set
    valBound .z z-isval E = z ≤s E
    valBound .(suc e) (suc-isval e v) E = Σ (λ E' → valBound e v E' × s E' ≤s E)
    valBound .(prod e1 e2) (pair-isval e1 e2 v1 v2) E = valBound e1 v1 (l-proj E) × valBound e2 v2 (r-proj E)
    valBound {τ1 ->s τ2} .(lam e) (lam-isval e) E = (v₁ : [] Source.|- τ1) (vv : val v₁)
                                                    (E1 : [] Pilot2.|- ⟨⟨ τ1 ⟩⟩) →
                                                    valBound v₁ vv E1 →
                                                    expBound (Source.subst e (Source.q v₁)) (app E E1)
    valBound .unit unit-isval E = Unit
    valBound .(delay e) (delay-isval e) E = expBound e E
    valBound .nil nil-isval E = nil ≤s E
    valBound .(x ::s xs) (cons-isval x xs v v₁) E = Σ (λ E' → Σ (λ E'' → (valBound x v E' × valBound xs v₁ E'') × (E' ::c E'') ≤s E))
    valBound .true true-isval E = true ≤s E
    valBound .false false-isval E = false ≤s E

    expBound : ∀{τ} → [] Source.|- τ → [] Pilot2.|- || τ || → Set
    expBound {τ} e b = (v₁ : [] Source.|- τ) (vv : val v₁) (n : Cost) →
                         evals e v₁ n → interp-Cost n ≤s l-proj b × valBound v₁ vv (r-proj b)

  mutual
    weakeningExp : ∀{τ} → (e : [] Source.|- τ) → (E E' : [] Pilot2.|- || τ ||) → expBound e E → E ≤s E' → expBound e E'
    weakeningExp e c1 c2 d c1≤c2 e' ve' n i = trans-s (fst (d e' ve' n i)) (cong-lproj c1≤c2) , 
                                                      weakeningVal e' ve' (r-proj c1) (r-proj c2) (snd (d e' ve' n i)) (cong-rproj c1≤c2)

    weakeningVal : ∀{τ} → (v : [] Source.|- τ) → (vv : val v) → (E E' : [] Pilot2.|- ⟨⟨ τ ⟩⟩) → valBound v vv E → E ≤s E' → valBound v vv E'
    weakeningVal {unit} unit unit-isval E E' vb e≤e' = <>
    weakeningVal {nat} .z z-isval E E' vb e≤e' = vb trans e≤e'
    weakeningVal {nat} .(suc e) (suc-isval e vv) E E' (i , vbi , si≤se) e≤e' = i , (vbi , (trans-s si≤se e≤e'))
    weakeningVal {susp τ} .(delay e) (delay-isval e) E E' vb e≤e' v₁ vv n x = weakeningExp e _ E' vb e≤e' v₁ vv n x
    weakeningVal {τ ->s τ₁} .(lam e) (lam-isval e) E E' vb e≤e' v₁ vv c1 x v₂ vv₁ n x₁ = (λ a va a' vba b b' n₁ x₂ →
                                                                                              fst (vb a va a' vba b b' n₁ x₂) trans cong-lproj (cong-app e≤e') ,
                                                                                              weakeningVal b b' (r-proj (app E a')) (r-proj (app E' a'))
                                                                                              (snd (vb a va a' vba b b' n₁ x₂)) (cong-rproj (cong-app e≤e')))
                                                                                           v₁ vv c1 x v₂ vv₁ n x₁
    weakeningVal {τ ×s τ₁} .(prod e1 e2) (pair-isval e1 e2 vv1 vv2) E E' vb e≤e' =
                    weakeningVal e1 vv1 (l-proj E) (l-proj E') (fst vb) (cong-lproj e≤e') ,
                    weakeningVal e2 vv2 (r-proj E) (r-proj E') (snd vb) (cong-rproj e≤e')
    weakeningVal {list τ} .nil nil-isval E E' vb e≤e' = vb trans e≤e'
    weakeningVal {list τ} .(x ::s xs) (cons-isval x xs vv vv₁) E E' (h , t , (hvb , tvb) , steps) e≤e' = h , (t , ((hvb , tvb) , (steps trans e≤e')))
    weakeningVal {bool} .true true-isval E E' vb e≤e' = vb trans e≤e'
    weakeningVal {bool} .false false-isval E E' vb e≤e' = vb trans e≤e'

  weakeningExp' : ∀{τ} {e : [] Source.|- τ} {E E' : [] Pilot2.|- || τ ||} → expBound e E → E ≤s E' → expBound e E'
  weakeningExp' eb e≤ = weakeningExp _ _ _ eb e≤

  weakeningVal' : ∀{τ} { v : [] Source.|- τ} (vv : val v) {E E' : [] Pilot2.|- ⟨⟨ τ ⟩⟩}
                → valBound v vv E → E ≤s E' → valBound v vv E'
  weakeningVal' vv v e = weakeningVal _ vv _ _ v e

  substVal : ∀{Γ} → (Θ : Source.sctx [] Γ) → Set
  substVal {Γ} Θ = {τ : _} (x : τ Source.∈ Γ) → val (Θ x)

  extend-substVal : ∀ {Γ' τ} {Θ : Source.sctx [] Γ'} {e : [] Source.|- τ}
                  → substVal Θ
                  → val e
                  → substVal (Source.lem3' Θ e)
  extend-substVal sv vv i0 = vv
  extend-substVal sv vv (iS x) = sv x

  extend-substVal2 : ∀ {Γ' τ1 τ2} {Θ : Source.sctx [] Γ'} {e : [] Source.|- τ1} {e' : [] Source.|- τ2}
                   → substVal Θ
                   → val e → val e'
                   → substVal (Source.lem4' Θ e e')
  extend-substVal2 sv vv vv' i0 = vv
  extend-substVal2 sv vv vv' (iS i0) = vv'
  extend-substVal2 sv vv vv' (iS (iS x)) = sv x

  extend-substVal3 : ∀ {Γ' τ1 τ2 τ3} {Θ : Source.sctx [] Γ'} {e : [] Source.|- τ1} {e' : [] Source.|- τ2} {e'' : [] Source.|- τ3}
                   → substVal Θ
                   → val e → val e' → val e''
                   → substVal (Source.lem5' Θ e e' e'')
  extend-substVal3 sv vv vv' vv'' i0 = vv
  extend-substVal3 sv vv vv' vv'' (iS i0) = vv'
  extend-substVal3 sv vv vv' vv'' (iS (iS i0)) = vv''
  extend-substVal3 sv vv vv' vv'' (iS (iS (iS x))) = sv x

  substBound : ∀{Γ} → (Θ : Source.sctx [] Γ) → substVal Θ → (Θ' : Pilot2.sctx [] ⟨⟨ Γ ⟩⟩c) → Set
  substBound {Γ} Θ vΘ Θ' = {τ : _} (x : τ Source.∈ Γ) → valBound (Θ x) (vΘ x) (Θ' (lookup x))

  extend-substBound : ∀{Γ τ} → {Θ : Source.sctx [] Γ} {vΘ : substVal Θ} {Θ' : Pilot2.sctx [] ⟨⟨ Γ ⟩⟩c}
                    → {e : [] Source.|- τ} {ve : val e} {E : [] Pilot2.|- ⟨⟨ τ ⟩⟩} 
                    → substBound Θ vΘ Θ'
                    → valBound e ve E
                    → substBound (Source.lem3' Θ e) (extend-substVal vΘ ve) (Pilot2.lem3' Θ' E)
  extend-substBound sb vb i0 = vb
  extend-substBound sb vb (iS x) = sb x

  extend-substBound2 : ∀{Γ τ1 τ2} → {Θ : Source.sctx [] Γ} {vΘ : substVal Θ} {Θ' : Pilot2.sctx [] ⟨⟨ Γ ⟩⟩c}
                     → {e : [] Source.|- τ1} {ve : val e} {e' : [] Source.|- τ2} {ve' : val e'}
                       {E : [] Pilot2.|- ⟨⟨ τ1 ⟩⟩} {E' : [] Pilot2.|- ⟨⟨ τ2 ⟩⟩}
                     → substBound Θ vΘ Θ'
                     → valBound e ve E → valBound e' ve' E'
                     → substBound (Source.lem4' Θ e e') (extend-substVal2 vΘ ve ve') (Pilot2.lem4' Θ' E E')
  extend-substBound2 sb vbE vbE' i0 = vbE
  extend-substBound2 sb vbE vbE' (iS i0) = vbE'
  extend-substBound2 sb vbE vbE' (iS (iS x)) = sb x

  extend-substBound3 : ∀{Γ τ1 τ2 τ3} → {Θ : Source.sctx [] Γ} {vΘ : substVal Θ} {Θ' : Pilot2.sctx [] ⟨⟨ Γ ⟩⟩c}
                     → {e : [] Source.|- τ1} {ve : val e} {e' : [] Source.|- τ2} {ve' : val e'} {e'' : [] Source.|- τ3} {ve'' : val e''}
                       {E : [] Pilot2.|- ⟨⟨ τ1 ⟩⟩} {E' : [] Pilot2.|- ⟨⟨ τ2 ⟩⟩} {E'' : [] Pilot2.|- ⟨⟨ τ3 ⟩⟩}
                     → substBound Θ vΘ Θ'
                     → valBound e ve E → valBound e' ve' E' → valBound e'' ve'' E''
                     → substBound (Source.lem5' Θ e e' e'') (extend-substVal3 vΘ ve ve' ve'') (Pilot2.lem5' Θ' E E' E'')
  extend-substBound3 sb vbE vbE' vbE'' i0 = vbE
  extend-substBound3 sb vbE vbE' vbE'' (iS i0) = vbE'
  extend-substBound3 sb vbE vbE' vbE'' (iS (iS i0)) = vbE''
  extend-substBound3 sb vbE vbE' vbE'' (iS (iS (iS x))) = sb x

  -- inversion lemma
  inv1 : ∀ {τ} {v v' : [] Source.|- τ} {n : Cost} → val v → evals v v' n → _≤s_{[]} (interp-Cost n) 0C
  inv1 z-isval z-evals = refl-s
  inv1 (suc-isval e v) (s-evals evals) = inv1 v evals
  inv1 (pair-isval e1 e2 v v₁) (pair-evals evals evals₁) = cong-+ (inv1 v evals) (inv1 v₁ evals₁) trans +-unit-l trans refl-s
  inv1 (lam-isval e) lam-evals = refl-s
  inv1 unit-isval unit-evals = refl-s
  inv1 (delay-isval e) delay-evals = refl-s
  inv1 nil-isval nil-evals = refl-s
  inv1 (cons-isval x xs v v₁) (cons-evals evals evals₁) = cong-+ (inv1 v evals) (inv1 v₁ evals₁) trans +-unit-l
  inv1 true-isval true-evals = refl-s
  inv1 false-isval false-evals = refl-s

  inv2 : ∀ {τ} {v e : [] Source.|- τ} {n : Cost} -> val v → evals v e n → v == e
  inv2 z-isval z-evals = Refl
  inv2 (suc-isval e₁ v) (s-evals evals) = ap suc (inv2 v evals)
  inv2 (pair-isval e1 e2 v v₁) (pair-evals evals evals₁) = ap2 prod (inv2 v evals) (inv2 v₁ evals₁)
  inv2 (lam-isval e₁) lam-evals = Refl
  inv2 unit-isval unit-evals = Refl
  inv2 (delay-isval e₁) delay-evals = Refl
  inv2 nil-isval nil-evals = Refl
  inv2 (cons-isval x xs v v₁) (cons-evals evals evals₁) = ap2 _::s_ (inv2 v evals) (inv2 v₁ evals₁)
  inv2 true-isval true-evals = Refl
  inv2 false-isval false-evals = Refl

  val-hprop : ∀ {τ} {v : [] Source.|- τ} → (d1 d2 : val v) → d1 == d2
  val-hprop z-isval z-isval = Refl
  val-hprop (suc-isval e d1) (suc-isval .e d2) = ap (suc-isval e) (val-hprop d1 d2)
  val-hprop (pair-isval e1 e2 d1 d2) (pair-isval .e1 .e2 d3 d4) = ap2 (pair-isval e1 e2) (val-hprop d1 d3) (val-hprop d2 d4)
  val-hprop (lam-isval e) (lam-isval .e) = Refl
  val-hprop unit-isval unit-isval = Refl
  val-hprop (delay-isval e) (delay-isval .e) = Refl
  val-hprop nil-isval nil-isval = Refl
  val-hprop (cons-isval x xs d1 d2) (cons-isval .x .xs d3 d4) = ap2 (cons-isval x xs) (val-hprop d1 d3) (val-hprop d2 d4)
  val-hprop true-isval true-isval = Refl
  val-hprop false-isval false-isval = Refl

  transport-valBound :  ∀{τ} {e e' : [] Source.|- τ} {d : val e} {d' : val e'}
                     → (α : e == e')
                     → transport val α d == d'
                     → (E : [] Pilot2.|- ⟨⟨ τ ⟩⟩)
                     → valBound e d E → valBound e' d' E
  transport-valBound Refl Refl E vb = vb

  Eq0C-≤0 : ∀ {n} → Equals0c n → _≤s_{[]} (interp-Cost n) 0C
  Eq0C-≤0 Eq0-0c = refl-s
  Eq0C-≤0 (Eq0-+c e e₁) = cong-+ (Eq0C-≤0 e) (Eq0C-≤0 e₁) trans +-unit-l

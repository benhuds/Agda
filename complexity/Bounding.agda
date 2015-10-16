{- PROOF OF BOUNDING THEOREM -}

open import Preliminaries
open import Source
open import Complexity
open import Translation
open import Bounding-Lemmas

module Bounding where

  boundingRec : ∀ {τ} (v : [] Source.|- nat) (val-v : val v)
                      (e0 : [] Source.|- τ)
                      (e1 : (nat :: susp τ :: []) Source.|- τ)
                      (E : [] Complexity.|- nat)
                      (E0 : [] Complexity.|- || τ ||)
                      (E1 : (nat :: || τ || :: []) Complexity.|- || τ ||)
              → valBound v val-v E → expBound e0 E0
              → ((v' : [] Source.|- nat) (val-v' : val v') (E' :  [] Complexity.|- nat) 
              → valBound v' val-v' E' → (r : [] Source.|- susp τ) (val-r : val r) (R :  [] Complexity.|- || τ ||)
              → valBound r val-r R
              → expBound (Source.subst e1 (Source.lem4 v' r)) (Complexity.subst E1 (Complexity.lem4 E' R)))
              → ((vbranch : [] Source.|- τ) (val-vbranch : val vbranch) (nbranch : Cost) 
              → evals-rec-branch e0 e1 v vbranch nbranch
              → (plusC 1C (interp-Cost nbranch) ≤s l-proj (rec E (1C +C E0) (1C +C E1))
                × (valBound vbranch val-vbranch (r-proj (rec E (1C +C E0) (1C +C E1))))))
  boundingRec .z z-isval e0 e1 E E0 E1 vbound e0bound e1bound vbranch val-vbranch nbranch (evals-rec-z evals-branch) = 
    (cong-+ refl-s (fst usee0bound ) trans l-proj-s) trans cong-lproj (rec-steps-z trans cong-rec vbound) , 
    weakeningVal' val-vbranch (snd usee0bound) (r-proj-s trans cong-rproj (rec-steps-z trans (cong-rec (vbound))))
    where usee0bound = (e0bound vbranch val-vbranch nbranch evals-branch)
  boundingRec .(suc v') (suc-isval v' val-v') e0 e1 E E0 E1 (E' , v'bound , sucE'≤E) e0bound e1bound vbranch val-vbranch nbranch (evals-rec-s evals-branch) = 
    (cong-+ refl-s (fst usee1bound) trans l-proj-s) trans cong-lproj (rec-steps-s trans cong-rec sucE'≤E) , 
    weakeningVal' val-vbranch (snd usee1bound) (r-proj-s trans cong-rproj (rec-steps-s trans cong-rec sucE'≤E)) where
      IH = boundingRec v' val-v' e0 e1 E' E0 E1 v'bound e0bound e1bound
      usee1bound = e1bound v' val-v' E' v'bound
                         (delay (rec v' e0 e1)) (delay-isval _) (rec E' (1C +C E0) (1C +C E1) )
                         (λ { vr vvr ._ (rec-evals{n1 = n1} {n2 = n2} D D') → 
                           let useIH = IH vr vvr n2 (transport (λ H → evals-rec-branch e0 e1 H vr n2) (! (fst (val-evals-inversion val-v' D))) D') 
                            in (cong-+ (Eq0C-≤0 (snd (val-evals-inversion val-v' D))) refl-s trans +-unit-l) trans fst useIH , snd useIH} ) 
                         vbranch val-vbranch nbranch evals-branch

  bounding : ∀{Γ τ} → (e : Γ Source.|- τ) → (Θ : Source.sctx [] Γ) 
                       → (a : substVal Θ) 
                       → (Θ' : Complexity.sctx [] ⟨⟨ Γ ⟩⟩c) 
                       → substBound Θ a Θ' 
                       → expBound (Source.subst e Θ) (Complexity.subst || e ||e Θ')
  bounding unit Θ a Θ' sb unit unit-isval 0c unit-evals = l-proj-s , <>
  bounding (var x) Θ a Θ' sb v vv c evals =
    inv1 (a x) evals trans l-proj-s ,
    weakeningVal' vv (transport-valBound (inv2 (a x) evals) (val-hprop (transport val (inv2 (a x) evals) (a x)) vv) _ (sb x)) r-proj-s
  bounding z Θ a Θ' sb .z z-isval .0c z-evals = l-proj-s , r-proj-s
  bounding (suc e) Θ a Θ' sb .(suc e₁) (suc-isval e₁ vv) n (s-evals evals) =
    fst IH trans l-proj-s ,
    (r-proj (Complexity.subst || e ||e Θ')) , (snd IH) , r-proj-s
    where
      IH = (bounding e Θ a Θ' sb _ vv _ evals)
  bounding (rec e e₁ e₂) Θ a Θ' sb e' val-e' ._ (rec-evals {v = v} arg-evals branch-evals) =
    cong-+ (fst IH1) (fst lemma) trans l-proj-s , weakeningVal' val-e' (snd lemma) r-proj-s
    where
      IH1 = bounding e Θ a Θ' sb _ (evals-val arg-evals) _ arg-evals
      lemma = boundingRec v (evals-val arg-evals) _ 
              (Source.subst e₂ (Source.s-extend (Source.s-extend Θ))) _ _ (Complexity.subst || e₂ ||e (Complexity.s-extend (Complexity.s-extend Θ')))
              (snd IH1)
              (bounding e₁ Θ a Θ' sb )
              (λ v' valv' E' valBoundv' r valr R valBoundR v'' valv'' c'' evals-rec →
              let IH3 = (bounding e₂ (Source.lem4' Θ v' r) (extend-substVal2 a valv' valr) (Complexity.lem4' Θ' E' R)
                        (extend-substBound2 sb valBoundv' valBoundR) v'' valv'' c'' (transport (λ x → evals x v'' c'')
                        (Source.subst-compose4 Θ v' r e₂) evals-rec))
              in (fst IH3 trans cong-refl (ap l-proj (! (Complexity.subst-compose4 Θ' E' R || e₂ ||e))) ,
                 weakeningVal' valv'' (snd IH3) (cong-rproj (cong-refl (! (Complexity.subst-compose4 Θ' E' R || e₂ ||e))))))
                 e' val-e' _ branch-evals
  bounding {τ = ρ ->s τ} (lam e) Θ a Θ' sb .(lam (Source.subst e (Source.s-extend Θ))) (lam-isval .(Source.subst e (Source.s-extend Θ))) .0c lam-evals = 
    l-proj-s ,
    (λ v₁ vv₁ E1 valbound1 v vv n body-evals →
    let IH = bounding e (Source.lem3' Θ v₁) (extend-substVal a vv₁)
             (Complexity.lem3' Θ' E1) (extend-substBound sb valbound1) 
             v vv n (transport (λ x → evals x v n) (Source.subst-compose Θ v₁ e) body-evals)
    in
      fst IH trans cong-lproj (cong-refl (! (Complexity.subst-compose Θ' E1 || e ||e)) trans lam-s trans cong-app r-proj-s) ,
      weakeningVal' vv (snd IH) (cong-rproj (cong-refl (! (Complexity.subst-compose Θ' E1 || e ||e)) trans lam-s trans cong-app r-proj-s)))
  bounding (app e1 e2) Θ a Θ' sb v val-v .((n0 +c n1) +c n)
           (app-evals {n0} {n1} {n} {τ2} {τ} {.(Source.subst e1 Θ)} {e1'} {.(Source.subst e2 Θ)} {v2} e1-evals e2-evals subst-evals) =
    cong-+ (cong-+ (fst IH1) (fst IH2)) (fst IH1a) trans l-proj-s ,
    weakeningVal' val-v (snd IH1a) r-proj-s
      where
        IH1 = (bounding e1 Θ a Θ' sb (lam e1') (lam-isval e1') n0 e1-evals)
        v2-val = evals-val e2-evals
        IH2 = (bounding e2 Θ a Θ' sb v2 v2-val n1 e2-evals)
        IH1a = snd IH1 v2 v2-val (r-proj (Complexity.subst || e2 ||e Θ')) (snd IH2) v val-v n subst-evals 
  bounding {Γ} {τ1 ×s τ2} (prod e1 e2) Θ a Θ' sb .(prod e3 e4) (pair-isval e3 e4 val-e3 val-e4) .(n1 +c n2) (pair-evals {n1} {n2} evals-c1 evals-c2) =
    cong-+ (fst IH1) (fst IH2) trans l-proj-s , 
    weakeningVal' val-e3 (snd IH1) (l-proj-s trans cong-lproj r-proj-s) , 
      weakeningVal' val-e4 (snd IH2) (r-proj-s trans cong-rproj r-proj-s)
    where
      IH1 = (bounding e1 Θ a Θ' sb _ val-e3 _ evals-c1)           
      IH2 = (bounding e2 Θ a Θ' sb _ val-e4 _ evals-c2)
  bounding (delay e) Θ a Θ' sb .(delay (Source.subst e Θ)) (delay-isval .(Source.subst e Θ)) .0c delay-evals =
    l-proj-s ,
    (λ v₁ vv n x → 
    let IH = bounding e Θ a Θ' sb v₁ vv n x  in 
    fst IH trans cong-lproj (r-proj-s trans refl-s) ,
    weakeningVal' vv (snd IH) (cong-rproj r-proj-s))
  bounding (force e) Θ a Θ' sb v vv ._ (force-evals {n1} {n2} {τ} {e'} {.v} {.(Source.subst e Θ)} evals evals₁) =
    (cong-+ (fst IH) (fst (snd IH v vv n2 evals₁)) trans l-proj-s) ,
    weakeningVal' vv (snd (snd IH v vv n2 evals₁)) r-proj-s
    where
      IH = (bounding e Θ a Θ' sb _ (delay-isval e') n1 evals)
  bounding {Γ} {τ} (split e0 e1) Θ a Θ' sb e' val-e' .(n1 +c n2) (split-evals {n1} {n2} {.τ} {τ1} {τ2} {.(Source.subst e0 Θ)} {v1} {v2} evals-in-c0 evals-in-c1) with evals-val evals-in-c0 | (bounding e0 Θ a Θ' sb (prod v1 v2) (evals-val evals-in-c0) _ evals-in-c0)
  ... | pair-isval ._ ._ val-v1 val-v2 | (IH11 , vb1 , vb2)
           = cong-+ IH11 (fst IH2) trans
             cong-+ refl-s (cong-lproj (cong-refl (! (Complexity.subst-compose3 Θ' || e1 ||e (l-proj (r-proj || e0 ||e)) (r-proj (r-proj || e0 ||e)))))) trans l-proj-s ,
             weakeningVal' val-e' (snd IH2)
             (cong-rproj (cong-refl
               (! (Complexity.subst-compose3 Θ' || e1 ||e (l-proj (r-proj || e0 ||e)) (r-proj (r-proj || e0 ||e))))) trans r-proj-s) where
           IH2 = bounding e1 (Source.lem4' Θ v1 v2)
                            (extend-substVal2 a val-v1 val-v2)
                            (Complexity.lem4' Θ' (l-proj (r-proj (Complexity.subst || e0 ||e Θ'))) (r-proj (r-proj (Complexity.subst || e0 ||e Θ'))))
                            (extend-substBound2 sb vb1 vb2)
                              e' val-e' n2 (transport (λ x → evals x e' n2) (Source.subst-compose3 Θ e1 v1 v2) evals-in-c1)
  bounding nil Θ a Θ' sb .nil nil-isval .0c nil-evals = l-proj-s , r-proj-s
  bounding (e ::s e₁) Θ a Θ' sb .(x ::s xs) (cons-isval x xs vv vv₁) ._ (cons-evals evals evals₁) =
           (cong-+ (fst IH1) (fst IH2) trans l-proj-s) ,
             (r-proj (Complexity.subst || e ||e Θ')) , r-proj (Complexity.subst || e₁ ||e Θ') , ((snd IH1 , snd IH2) , r-proj-s)
    where
      IH1 = (bounding e Θ a Θ' sb _ vv _ evals) 
      IH2 = (bounding e₁ Θ a Θ' sb _ vv₁ _ evals₁) 
  bounding (listrec e e₁ e₂) Θ a Θ' sb v vv ._ (listrec-evals arg-evals branch-evals) = (cong-+ (fst IH1) {!!} trans l-proj-s) , weakeningVal' vv {!!} r-proj-s
    where
      IH1 = bounding e Θ a Θ' sb _ (evals-val arg-evals) _ arg-evals
  bounding true Θ a Θ' sb .true true-isval .0c true-evals = l-proj-s , <>
  bounding false Θ a Θ' sb .false false-isval .0c false-evals = l-proj-s , <>

  boundingListRec : ∀ {τ τ₁} (v : [] Source.|- list τ) (vv : val v)
                             (e₁ : [] Source.|- τ) (e₂ : τ₁ :: list τ₁ :: susp τ :: [] Source.|- τ)
                             (E : [] Complexity.|- list || τ ||)
                             (E₁ : [] Complexity.|- || τ ||)
                             (E₂ : || τ₁ || :: list || τ₁ || :: || τ || :: [] Complexity.|- || τ ||)
                             --→ valBound v vv E → expBound e₁ E₁
                             → (vbranch : [] Source.|- τ) (val-vbranch : val vbranch) (nbranch : Cost)
                             --→ --evals-listrec-branch e₁ e₂ v vbranch nbranch
                             → plusC 1C (interp-Cost nbranch) ≤s l-proj (listrec E (1C +C E₁) (1C +C E₂))
                               × valBound vbranch val-vbranch (r-proj (listrec E (1C +C E₁) (1C +C E₂))) 
                               --plusC 1C (interp-Cost nbranch) ≤s l-proj (listrec E (1C +C E₁) (1C +C E₂))
                               --× valBound vbranch val-vbranch (r-proj (listrec E (1C +C E₁) (1C +C E₂)))
  boundingListRec v vv e₁ e₂ E E₁ E₂ vbranch vvbranch nbranch = {!!}


{-
  boundingRec : ∀ {τ} (v : [] Source.|- nat) (val-v : val v)
                      (e0 : [] Source.|- τ)
                      (e1 : (nat :: susp τ :: []) Source.|- τ)
                      (E : [] Complexity.|- nat)
                      (E0 : [] Complexity.|- || τ ||)
                      (E1 : (nat :: || τ || :: []) Complexity.|- || τ ||)
              → valBound v val-v E → expBound e0 E0
              → ((v' : [] Source.|- nat) (val-v' : val v') (E' :  [] Complexity.|- nat) 
              → valBound v' val-v' E' → (r : [] Source.|- susp τ) (val-r : val r) (R :  [] Complexity.|- || τ ||)
              → valBound r val-r R
              → expBound (Source.subst e1 (Source.lem4 v' r)) (Complexity.subst E1 (Complexity.lem4 E' R)))
              → ((vbranch : [] Source.|- τ) (val-vbranch : val vbranch) (nbranch : Cost) 
              → evals-rec-branch e0 e1 v vbranch nbranch
              → (plusC 1C (interp-Cost nbranch) ≤s l-proj (rec E (1C +C E0) (1C +C E1))
                × (valBound vbranch val-vbranch (r-proj (rec E (1C +C E0) (1C +C E1))))))

  boundingListRec : ∀ {τ τ'} (v : [] Source.|- τ) (vv : val v)
                             (e₁ : [] Source.|- τ) (e₂ : τ₁ :: list τ₁ :: susp τ :: [] Source.|- τ)
                             (E : [] Complexity.|- τ)
                             (E₁ : [] Complexity.|- || τ ||)
                             (E₂ : || τ₁ || :: list || τ₁ || :: || τ || :: [] Complexity.|- || τ ||)
                             → valBound v vv E → expBound e₁ E₁
                             → expBound (
                             → ((vbranch : [] Source.|- τ) (val-vbranch : val vbranch) (nbranch : Cost) 
                             → evals-rec-branch e₁ e₂ v vbranch nbranch
                             plusC 1C (interp-Cost nbranch) ≤s l-proj (listRec E (1C +C E0) (1C +C E1))
                             × valBound vbranch val-vbranch (r-proj (rec E (1C +C E0) (1C +C E1)))

 plusC 1C (interp-Cost .n2) ≤s
      l-proj
      (listrec (r-proj (Complexity.subst || e ||e Θ'))
       (prod (plusC 1C (l-proj (Complexity.subst || e₁ ||e Θ')))
        (r-proj (Complexity.subst || e₁ ||e Θ')))
       (prod
        (plusC 1C
         (l-proj
          (Complexity.subst || e₂ ||e
           (Complexity.s-extend
            (Complexity.s-extend (Complexity.s-extend Θ'))))))
        (r-proj
         (Complexity.subst || e₂ ||e
          (Complexity.s-extend
           (Complexity.s-extend (Complexity.s-extend Θ')))))))
-}

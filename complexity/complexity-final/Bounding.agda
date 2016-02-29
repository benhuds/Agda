{- PROOF OF BOUNDING THEOREM WITH NEW COMPLEXITY LANGUAGE -}

open import Preliminaries
open import Source
open import Pilot2
open import Translation
open import Bounding-Lemmas

module Bounding where

  boundingRec : ∀ {τ} (v : [] Source.|- nat) (val-v : val v)
                      (e0 : [] Source.|- τ)
                      (e1 : (nat :: susp τ :: []) Source.|- τ)
                      (E : [] Pilot2.|- nat)
                      (E0 : [] Pilot2.|- || τ ||)
                      (E1 : (nat :: || τ || :: []) Pilot2.|- || τ ||)
              → valBound v val-v E → expBound e0 E0
              → ((v' : [] Source.|- nat) (val-v' : val v') (E' :  [] Pilot2.|- nat) → valBound v' val-v' E'
                → (r : [] Source.|- susp τ) (val-r : val r) (R :  [] Pilot2.|- || τ ||) → valBound r val-r R
                → expBound (Source.subst e1 (Source.lem4 v' r)) (Pilot2.subst E1 (Pilot2.lem4 E' R)))
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
                            in (cong-+ (Eq0C-≤0 (snd (val-evals-inversion val-v' D))) refl-s trans +-unit-l) trans fst useIH , snd useIH } )
                         vbranch val-vbranch nbranch evals-branch

  boundingListRec : ∀ {τ τ'} (v : [] Source.|- list τ') (vv : val v)
                             (e0 : [] Source.|- τ)
                             (e1 : τ' :: list τ' :: susp τ :: [] Source.|- τ)
                             (E : [] Pilot2.|- list ⟨⟨ τ' ⟩⟩)
                             (E0 : [] Pilot2.|- || τ ||)
                             (E1 : ⟨⟨ τ' ⟩⟩ :: list ⟨⟨ τ' ⟩⟩ :: || τ || :: [] Pilot2.|- || τ ||)
                             → valBound v vv E → expBound e0 E0
                             → ((h' : []  Source.|- τ') (vh' : val h') (H' : [] Pilot2.|- ⟨⟨ τ' ⟩⟩)
                               → valBound h' vh' H'
                               → (v' : [] Source.|- list τ') (vv' : val v') (V' : [] Pilot2.|- list ⟨⟨ τ' ⟩⟩)
                               → valBound v' vv' V'
                               → (r : [] Source.|- susp τ) (vr : val r) (R : [] Pilot2.|- || τ ||)
                               → valBound r vr R
                               → expBound (Source.subst e1 (Source.lem5 h' v' r)) (Pilot2.subst E1 (Pilot2.lem5 H' V' R)))
                             → (vbranch : [] Source.|- τ)  (vvbranch : val vbranch) (nbranch : Cost)
                             → evals-listrec-branch e0 e1 v vbranch nbranch
                             → plusC 1C (interp-Cost nbranch) ≤s l-proj (listrec E (1C +C E0) (1C +C E1))
                               × valBound vbranch vvbranch (r-proj (listrec E (1C +C E0) (1C +C E1)))
  boundingListRec .nil nil-isval e0 e1 E E0 E1 vbv e0b e1b vbranch vvbranch n (evals-listrec-nil evals-branch) =
    ((cong-+ refl-s (fst usee0bound) trans l-proj-s) trans cong-lproj (listrec-steps-nil trans cong-listrec vbv)) ,
    weakeningVal' vvbranch (snd usee0bound) (r-proj-s trans cong-rproj (listrec-steps-nil trans cong-listrec vbv))
    where usee0bound = e0b vbranch vvbranch n evals-branch
  boundingListRec .(x ::s xs) (cons-isval x xs vv vv₁) e0 e1 E E0 E1 (h' , t' , (vbxh' , vbxst') , h'::t'≤sE)
    e0b e1b vbranch vvbranch nbranch (evals-listrec-cons evals-branch) =
      (cong-+ refl-s (fst usee1bound) trans l-proj-s) trans cong-lproj (listrec-steps-cons trans cong-listrec h'::t'≤sE) ,
      weakeningVal' vvbranch (snd usee1bound) (r-proj-s trans cong-rproj (listrec-steps-cons trans cong-listrec h'::t'≤sE))
      where
        IH = boundingListRec xs vv₁ e0 e1 t' E0 E1 vbxst' e0b e1b
        usee1bound = e1b x vv h' vbxh' xs vv₁ t' vbxst'
                     (delay (listrec xs e0 e1)) (delay-isval _) (listrec t' (1C +C E0) (1C +C E1))
                     (λ { vr vvr ._ (listrec-evals {_} {n2} D D') →
                     let useIH = IH vr vvr n2 (transport (λ H → evals-listrec-branch e0 e1 H vr n2) (! (fst (val-evals-inversion vv₁ D))) D')
                     in (cong-+ (Eq0C-≤0 (snd (val-evals-inversion vv₁ D))) refl-s trans +-unit-l) trans fst useIH , snd useIH } )
                     vbranch vvbranch nbranch evals-branch

  bounding : ∀{Γ τ} → (e : Γ Source.|- τ) → (Θ : Source.sctx [] Γ) 
                       → (a : substVal Θ) 
                       → (Θ' : Pilot2.sctx [] ⟨⟨ Γ ⟩⟩c) 
                       → substBound Θ a Θ' 
                       → expBound (Source.subst e Θ) (Pilot2.subst || e ||e Θ')
  bounding unit Θ a Θ' sb .unit unit-isval .0c unit-evals = l-proj-s , <>
  bounding (var x) Θ a Θ' sb v vv c evals =
    inv1 (a x) evals trans l-proj-s ,
    weakeningVal' vv (transport-valBound (inv2 (a x) evals) (val-hprop (transport val (inv2 (a x) evals) (a x)) vv) _ (sb x)) r-proj-s
  bounding z Θ a Θ' sb .z z-isval .0c z-evals = l-proj-s , r-proj-s
  bounding (suc e) Θ a Θ' sb .(suc e₁) (suc-isval e₁ vv) n (s-evals evals) =
    fst IH trans l-proj-s ,
    (r-proj (Pilot2.subst || e ||e Θ')) , (snd IH) , r-proj-s
    where
      IH = (bounding e Θ a Θ' sb _ vv _ evals)
  bounding (rec e e₁ e₂) Θ a Θ' sb e' val-e' ._ (rec-evals {v = v} arg-evals branch-evals) =
    cong-+ (fst IH1) (fst lemma) trans l-proj-s , weakeningVal' val-e' (snd lemma) r-proj-s
    where
      IH1 = bounding e Θ a Θ' sb _ (evals-val arg-evals) _ arg-evals
      lemma = boundingRec v (evals-val arg-evals) _ 
              (Source.subst e₂ (Source.s-extend (Source.s-extend Θ))) _ _ (Pilot2.subst || e₂ ||e (Pilot2.s-extend (Pilot2.s-extend Θ')))
              (snd IH1)
              (bounding e₁ Θ a Θ' sb )
              (λ v' valv' E' valBoundv' r valr R valBoundR v'' valv'' c'' evals-rec →
              let IH3 = (bounding e₂ (Source.lem4' Θ v' r) (extend-substVal2 a valv' valr) (Pilot2.lem4' Θ' E' R)
                        (extend-substBound2 sb valBoundv' valBoundR) v'' valv'' c'' (transport (λ x → evals x v'' c'')
                        (Source.subst-compose4 Θ v' r e₂) evals-rec))
              in (fst IH3 trans cong-lproj (subst-compose4-r Θ' E' R || e₂ ||e)) , 
                 weakeningVal' valv'' (snd IH3)  (cong-rproj (subst-compose4-r Θ' E' R || e₂ ||e)))
                 e' val-e' _ branch-evals
  bounding (lam e) Θ a Θ' sb .(lam (Source.subst e (Source.s-extend Θ))) (lam-isval .(Source.subst e (Source.s-extend Θ))) .0c lam-evals =
    l-proj-s ,
    (λ v₁ vv₁ E1 valbound1 v vv n body-evals →
         let IH : _
             IH
               = bounding e (Source.lem3' Θ v₁) (extend-substVal a vv₁)
                 (Pilot2.lem3' Θ' E1) (extend-substBound sb valbound1) v vv n
                 (transport (λ x → evals x v n) (subst-compose Θ v₁ e) body-evals)
         in
           fst IH trans cong-lproj (subst-compose-r Θ' E1 || e ||e trans lam-s trans cong-app r-proj-s) ,
           weakeningVal' vv (snd IH) (cong-rproj (subst-compose-r Θ' E1 || e ||e trans lam-s trans cong-app r-proj-s)))
  bounding (app e1 e2) Θ a Θ' sb v val-v .((n0 +c n1) +c n)
           (app-evals {n0} {n1} {n} {τ2} {τ} {.(Source.subst e1 Θ)} {e1'} {.(Source.subst e2 Θ)} {v2} e1-evals e2-evals subst-evals) =
    cong-+ (cong-+ (fst IH1) (fst IH2)) (fst IH1a) trans l-proj-s ,
    weakeningVal' val-v (snd IH1a) r-proj-s
      where
        IH1 = (bounding e1 Θ a Θ' sb (lam e1') (lam-isval e1') n0 e1-evals)
        v2-val = evals-val e2-evals
        IH2 = (bounding e2 Θ a Θ' sb v2 v2-val n1 e2-evals)
        IH1a = snd IH1 v2 v2-val (r-proj (Pilot2.subst || e2 ||e Θ')) (snd IH2) v val-v n subst-evals 
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
  ... | pair-isval ._ ._ val-v1 val-v2 | (IH11 , vb1 , vb2) = 
    (cong-+ IH11 (fst IH2) trans cong-+ refl-s (cong-lproj (subst-compose3-r Θ' || e1 ||e (l-proj (r-proj || e0 ||e)) (r-proj (r-proj || e0 ||e))))) trans l-proj-s ,
    weakeningVal' val-e' (snd IH2) (cong-rproj (subst-compose3-r Θ' || e1 ||e (l-proj (r-proj || e0 ||e)) (r-proj (r-proj || e0 ||e))) trans r-proj-s)
    where
      IH2 = bounding e1 (Source.lem4' Θ v1 v2) (extend-substVal2 a val-v1 val-v2)
            (Pilot2.lem4' Θ' (l-proj (r-proj (Pilot2.subst || e0 ||e Θ'))) (r-proj (r-proj (Pilot2.subst || e0 ||e Θ'))))
            (extend-substBound2 sb vb1 vb2)
            e' val-e' n2 (transport (λ x → evals x e' n2) (Source.subst-compose3 Θ e1 v1 v2) evals-in-c1)
  bounding nil Θ a Θ' sb .nil nil-isval .0c nil-evals = l-proj-s , r-proj-s
  bounding (e ::s e₁) Θ a Θ' sb .(x ::s xs) (cons-isval x xs vv vv₁) ._ (cons-evals evals evals₁) =
           (cong-+ (fst IH1) (fst IH2) trans l-proj-s) ,
             (r-proj (Pilot2.subst || e ||e Θ')) , r-proj (Pilot2.subst || e₁ ||e Θ') , ((snd IH1 , snd IH2) , r-proj-s)
    where
      IH1 = (bounding e Θ a Θ' sb _ vv _ evals) 
      IH2 = (bounding e₁ Θ a Θ' sb _ vv₁ _ evals₁)
  bounding (listrec e e₁ e₂) Θ a Θ' sb v vv ._ (listrec-evals {v = k} arg-evals branch-evals) =
    (cong-+ (fst IH1) (fst lemma) trans l-proj-s) , weakeningVal' vv (snd lemma) r-proj-s
    where
      IH1 = bounding e Θ a Θ' sb _ (evals-val arg-evals) _ arg-evals
      lemma = boundingListRec k (evals-val arg-evals) _
              (Source.subst e₂ (Source.s-extend (Source.s-extend (Source.s-extend Θ)))) _ _
              (Pilot2.subst || e₂ ||e (Pilot2.s-extend (Pilot2.s-extend (Pilot2.s-extend Θ'))))
              (snd IH1)
              (bounding e₁ Θ a Θ' sb)
              (λ h' vh' H' vbh'H' v' vv' V' vbv'V' r vr R vbrR v₁ vv₁ n x₂ →
              let IH3 = bounding e₂ (Source.lem5' Θ h' v' r) (extend-substVal3 a vh' vv' vr) (Pilot2.lem5' Θ' H' V' R)
                        (extend-substBound3 sb vbh'H' vbv'V' vbrR) v₁ vv₁ n
                        (transport (λ x → evals x v₁ n) (Source.subst-compose5 Θ e₂ h' v' r) x₂)
              in
              fst IH3 trans cong-lproj (subst-compose5-r Θ' || e₂ ||e H' V' R) ,
              weakeningVal' vv₁ (snd IH3) (cong-rproj (subst-compose5-r Θ' || e₂ ||e H' V' R))) v vv _ branch-evals
  bounding true Θ a Θ' sb .true true-isval .0c true-evals = l-proj-s , r-proj-s
  bounding false Θ a Θ' sb .false false-isval .0c false-evals = l-proj-s , r-proj-s

{- INTERPRETATION OF NEW COMPLEXITY LANGUAGE -}

open import Preliminaries
--open import Preorder-Max
open import Preorder
open import Pilot2

module Interpretation where

  -- interpret complexity types as preorders
  [_]t : CTp → PREORDER
  [ unit ]t = unit-p
  [ nat ]t = Nat , ♭nat-p
  [ τ ->c τ₁ ]t = [ τ ]t ->p [ τ₁ ]t
  [ τ ×c τ₁ ]t = [ τ ]t ×p [ τ₁ ]t
  [ list τ ]t = Nat , nat-p
  [ bool ]t = Bool , bool-p
  [ C ]t = Nat , nat-p
  [ rnat ]t = Nat , nat-p

  [_]tm : ∀ {A} → CTpM A → Preorder-max-str (snd [ A ]t)
  [ runit ]tm = unit-pM
  [ rn ]tm = nat-pM
  [ e ×cm e₁ ]tm = axb-pM [ e ]tm [ e₁ ]tm
  [ _->cm_ e ]tm = mono-pM {!!} [ e ]tm
  
  -- interpret contexts as preorders
  [_]c : Ctx → PREORDER
  [ [] ]c = unit-p
  [ τ :: Γ ]c = [ Γ ]c ×p [ τ ]t

{-[ Θ ]s : Monotone [ Γ ]  [ Γ' ]
  [ ρ ]r : same
  interpE ren e ρ k == interpE e (interpR ρ) k-}

  el : PREORDER → Set
  el = fst

  PREORDER≤ : (PA : PREORDER) → el PA → el PA → Set
  PREORDER≤ PA = Preorder-str.≤ (snd PA)

  lookup : ∀{Γ τ} → τ ∈ Γ → el ([ Γ ]c ->p [ τ ]t)
  lookup (i0 {Γ} {τ}) = snd' id --snd' {[ (τ :: Γ) ]c} {[ Γ ]c} {_} id
  lookup (iS {Γ} {τ} {τ1} x) = comp {[ (τ1 :: Γ) ]c} {_} {_} (fst' {[ (τ1 :: Γ) ]c} {_} {[ τ1 ]t} id) (lookup x)

  interpR : ∀ {Γ Γ'} → (ρ : rctx Γ Γ') → MONOTONE [ Γ' ]c [ Γ ]c
  interpR {Γ} {Γ'} ρ = {!!}

  interpS : ∀ {Γ Γ'} → (Θ : sctx Γ Γ') → MONOTONE [ Γ' ]c [ Γ ]c
  interpS Θ = monotone (λ x → {!Θ !}) (λ x y x₁ → {!!})

  interpE : ∀{Γ τ} → Γ |- τ → el ([ Γ ]c ->p [ τ ]t)
  interpE unit = monotone (λ x → <>) (λ x y x₁ → <>)
  interpE 0C = monotone (λ x → Z) (λ x y x₁ → <>)
  interpE 1C = monotone (λ x → S Z) (λ x y x₁ → <>)
  interpE (plusC e e₁) = monotone (λ x → Monotone.f (interpE e) x + Monotone.f (interpE e₁) x) (λ x y x₁ → {!!})
  interpE (var x) = lookup x
  interpE z = monotone (λ x → Z) (λ x y x₁ → <>)
  interpE (s e) = monotone (λ x → S (Monotone.f (interpE e) x)) {!!}
  interpE (rec e e₁ e₂) = {!!}
--monotone (λ x → natrec (Monotone.f (interpE e₁) x) (λ n x₂ → Monotone.f (interpE e₂) ((x , x₂) , n)) (Monotone.f (interpE e) x)) (λ x y x₁ → {!!})
  interpE (lam e) = lam' (interpE e)
  interpE (app e e₁) = app' (interpE e) (interpE e₁)
  interpE rz = z'
  interpE (rsuc e) = suc' (interpE e)
  interpE (rrec e e₁ e₂ P) = {!!}
  interpE (prod e e₁) = pair' (interpE e) (interpE e₁)
  interpE (l-proj e) = fst' (interpE e)
  interpE (r-proj e) = snd' (interpE e)
  interpE nil = monotone (λ x → Z) (λ x y x₁ → <>)
  interpE (e ::c e₁) = {!!}
  interpE (listrec e e₁ e₂) = {!!}
  interpE true = monotone (λ x → True) (λ x y x₁ → <>)
  interpE false = monotone (λ x → False) (λ x y x₁ → <>)
  interpE (max runit e1 e2) = {!!}
  interpE (max rn e1 e2) = {!!}
  interpE (max (τ ×cm τ₁) e1 e2) = {!!}
  interpE (max (_->cm_ τ) e1 e2) = {!!}

  sound : ∀ {Γ τ} (e e' : Γ |- τ) → e ≤s e' → PREORDER≤ ([ Γ ]c ->p [ τ ]t) (interpE e) (interpE e')
  sound {_} {τ} e .e refl-s k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {Γ} {τ} e e' (trans-s {.Γ} {.τ} {.e} {e''} {.e'} d d₁) k =
        Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE e) k) (Monotone.f (interpE e'') k) (Monotone.f (interpE e') k)
        (sound e e'' d k) (sound e'' e' d₁ k)
  sound ._ ._ (plus-s d d₁) k = {!!}
  sound {_} {τ} e .e (cong-refl Refl) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound .(plusC 0C e') e' +-unit-l k = Preorder-str.refl (snd [ rnat ]t) (Monotone.f (interpE e') k)
  sound e .(plusC 0C e) +-unit-l' k = Preorder-str.refl (snd [ rnat ]t) (Monotone.f (interpE e) k)
  sound {_} {.C} .(plusC e' 0C) e' +-unit-r k = {!!}
  sound e .(plusC e 0C) +-unit-r' k = {!!}
  sound {_} {.C} ._ ._ +-assoc k = {!!}
  sound ._ ._ +-assoc' k = {!!}
  sound {_} {.C} ._ ._ refl-+ k = {!!}
  sound ._ ._ (cong-+ d d₁) k = {!!}
  sound {Γ} {τ} ._ ._ (cong-lproj {.Γ} {.τ} {_} {e} {e'} d) k = fst (sound e e' d k)
  sound {Γ} {τ} ._ ._ (cong-rproj {.Γ} {_} {.τ} {e} {e'} d) k = snd (sound e e' d k)
  sound {Γ} {τ} ._ ._ (cong-app {.Γ} {τ'} {.τ} {e} {e'} {e1} d) k = sound e e' d k (Monotone.f (interpE e1) k)
  sound {Γ} {τ} ._ ._ (ren-cong {.Γ} {Γ'} {.τ} {e1} {e2} {ρ} d) k = {!!}
  sound ._ ._ (subst-cong {_} {_} {_} {e1} {e2} {Θ} d) k = {!!}
  sound ._ ._ (subst-cong2 x) k = {!!}
  sound {Γ} {τ} ._ ._ (cong-rec {.Γ} {.τ} {e} {e'} {e0} {e1} d) k = {!!}
  sound ._ ._ (cong-listrec d) k = {!!}
  sound {Γ} {τ} ._ ._ (lam-s {.Γ} {τ'} {.τ} {e} {e2}) k = {!!}
  sound {Γ} {τ} e ._ (l-proj-s {.Γ}) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {Γ} {τ} e ._ (r-proj-s {.Γ}) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {_} {τ} e ._ rec-steps-z k = {!!} --Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound ._ ._ rec-steps-s k = {!!}
  sound e ._ listrec-steps-nil k = {!!}
  sound ._ ._ listrec-steps-cons k = {!!}
  sound .(ren (ren e ρ2) ρ1) ._ (ren-comp-l ρ1 ρ2 e) k = {!!}
  sound ._ .(ren (ren e ρ2) ρ1) (ren-comp-r ρ1 ρ2 e) k = {!!}
  sound {Γ} {τ} e ._ (subst-id-l {.Γ} {.τ} .e) k = {!!} --sound e (subst e ids) {!!} k
  sound ._ e' (subst-id-r .e') k = {!!}
  sound .(ren (subst e Θ) ρ) ._ (subst-rs-l ρ Θ e) k = {!!}
  sound ._ .(ren (subst e Θ) ρ) (subst-rs-r ρ Θ e) k = {!!}
  sound .(subst (ren e ρ) Θ) ._ (subst-sr-l Θ ρ e) k = {!!}
  sound ._ .(subst (ren e ρ) Θ) (subst-sr-r Θ ρ e) k = {!!}
  sound ._ .(subst (subst e Θ2) Θ1) (subst-ss-l Θ1 Θ2 e) k = {!!}
  sound .(subst (subst e Θ2) Θ1) ._ (subst-ss-r Θ1 Θ2 e) k = {!!}
  sound ._ .(subst e (lem3' Θ v)) (subst-compose-l Θ v e) k = {!!}
  sound .(subst e (lem3' Θ v)) ._ (subst-compose-r Θ v e) k = {!!}
  sound ._ .(subst e1 (lem3' (lem3' Θ v2) v1)) (subst-compose2-l Θ e1 v1 v2) k = {!!}
  sound .(subst e1 (lem3' (lem3' Θ v2) v1)) ._ (subst-compose2-r Θ e1 v1 v2) k = {!!}
  sound ._ .(subst e1 (lem3' (lem3' Θ (subst v2 Θ)) (subst v1 Θ))) (subst-compose3-l Θ e1 v1 v2) k = {!!}
  sound .(subst e1 (lem3' (lem3' Θ (subst v2 Θ)) (subst v1 Θ))) ._ (subst-compose3-r Θ e1 v1 v2) k = {!!}
  sound ._ .(subst e2 (lem3' (lem3' Θ r) v')) (subst-compose4-l Θ v' r e2) k = {!!}
  sound .(subst e2 (lem3' (lem3' Θ r) v')) ._ (subst-compose4-r Θ v' r e2) k = {!!}
  sound ._ .(subst e (lem3' (lem3' (lem3' Θ v3) v2) v1)) (subst-compose5-l Θ e v1 v2 v3) k = {!!}
  sound .(subst e (lem3' (lem3' (lem3' Θ v3) v2) v1)) ._ (subst-compose5-r Θ e v1 v2 v3) k = {!!}

{-old stuff which i may or may not need later

  cong-lemma : ∀ {Γ τ τ'}
             → (e : (τ :: Γ) |- τ')
             → (e1 e2 : Γ |- τ)
             → e1 ≤s e2
             → (k : fst (interpC Γ))
             → Preorder-max-str.≤ (snd (interp τ)) {!!} {!!}
  cong-lemma = {!!}

{-
Preorder-max-str.≤ (snd (interp .τ))
      (Monotone.f (interpE (subst (lem3 e1) e)) k)
      (Monotone.f (interpE (subst (lem3 e2) e)) k)
-}

  sound : ∀ {Γ τ} (e e' : Γ |- τ) → e ≤s e' → PREORDER≤ (interpC Γ ->p interp τ) (interpE e) (interpE e')
  sound e e' s = ?
{-  sound {_} {τ} .e' e' (refl-s .e') k = Preorder-max-str.refl (snd (interp τ)) (Monotone.f (interpE e') k)
  sound {_} {τ} e e' (trans-s .e e'' .e' p p₁) k = Preorder-max-str.trans (snd (interp τ)) (Monotone.f (interpE e) k)
                                                     (Monotone.f (interpE e'') k) (Monotone.f (interpE e') k)
                                                     (sound e e'' p k) (sound e'' e' p₁ k)
  sound .(subst (lem3 e1) e) .(subst (lem3 e2) e) (cong-s e e1 e2 p) k = Monotone.is-monotone {!!} (subst (lem3 e1) e) (subst (lem3 e2) e) cong-s
  sound .(subst (lem3 e2) e) .(app (lam e) e2) (lam-s e e2) k = {!!}
  sound {_} {τ} e .(l-proj (prod e e2)) (l-proj-s .e e2) k = Preorder-max-str.refl (snd (interp τ)) (Monotone.f (interpE e) k)
  sound {_} {τ} e .(r-proj (prod e1 e)) (r-proj-s e1 .e) k = Preorder-max-str.refl (snd (interp τ)) (Monotone.f (interpE e) k)
  sound .(subst (lem4 e (rec e e0 e1)) e1) .(rec (suc e) e0 e1) (rec-steps-s e e0 e1) k = {!!}
  sound e .(rec z e e1) (rec-steps-z .e e1) k = {!!}
-}
-}

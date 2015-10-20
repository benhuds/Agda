{- INTERPRETATION -}

open import Preliminaries
open import Preorder-Max
open import Complexity

module Interpretation where

  -- interpret complexity types as preorders
  [_]t : CTp → PREORDER
  [ unit ]t = unit-p
  [ nat ]t = Nat , nat-p
  [ A ->c B ]t = [ A ]t ->p [ B ]t
  [ A ×c B ]t = [ A ]t ×p [ B ]t
  [ list A ]t = Nat , nat-p
  [ bool ]t = unit-p
  [ C ]t = Nat , nat-p
  
  -- interpret contexts as preorders
  [_]c : Ctx → PREORDER
  [ [] ]c = unit-p
  [ τ :: Γ ]c = [ Γ ]c ×p [ τ ]t 

  el : PREORDER → Set
  el = fst

  PREORDER≤ : (PA : PREORDER) → el PA → el PA → Set
  PREORDER≤ PA = Preorder-max-str.≤ (snd PA)

  lookup : ∀{Γ τ} → τ ∈ Γ → el ([ Γ ]c ->p [ τ ]t)
  lookup (i0 {Γ} {τ}) = snd' {[ (τ :: Γ) ]c} {[ Γ ]c} {_} id
  lookup (iS {Γ} {τ} {τ1} x) = comp {[ (τ1 :: Γ) ]c} {_} {_} (fst' {[ (τ1 :: Γ) ]c} {_} {[ τ1 ]t} id) (lookup x)

  interpE : ∀{Γ τ} → Γ |- τ → el ([ Γ ]c ->p [ τ ]t)
  interpE unit = monotone (λ x → <>) (λ x y x₁ → <>)
  interpE 0C = monotone (λ x → Z) (λ x y x₁ → <>)
  interpE 1C = monotone (λ x → S Z) (λ x y x₁ → <>)
  interpE (plusC e e₁) = monotone (λ x → {!!} Nat.+ {!!}) {!!}
  interpE (var x) = lookup x
  interpE z = monotone (λ x → Z) (λ x y x₁ → <>)
  interpE (suc e) = monotone (λ x → S {!!}) (λ x y x₁ → {!!})
  interpE (rec e e₁ e₂) = {!!}
  interpE (lam e) = lam' (interpE e)
  interpE (app e e₁) = app' (interpE e) (interpE e₁)
  interpE (prod e e₁) = pair' (interpE e) (interpE e₁)
  interpE (l-proj e) = fst' (interpE e)
  interpE (r-proj e) = snd' (interpE e)
  interpE nil = {!!}
  interpE (e ::c e₁) = {!!}
  interpE (listrec e e₁ e₂) = {!!}
  interpE true = {!!}
  interpE false = {!!}

  sound : ∀ {Γ τ} (e e' : Γ |- τ) → e ≤s e' → PREORDER≤ ([ Γ ]c ->p [ τ ]t) (interpE e) (interpE e')
  sound {_} {τ} e .e refl-s k = Preorder-max-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {_} {τ} e e' (trans-s s s₁) k = {!!}
  sound ._ ._ (plus-s s s₁) x = {!!}
  sound e e' (cong-refl x) x₁ = {!!}
  sound .(plusC 0C e') e' +-unit-l x = {!!}
  sound e .(plusC 0C e) +-unit-l' x = {!!}
  sound .(plusC e' 0C) e' +-unit-r x = {!!}
  sound e .(plusC e 0C) +-unit-r' x = {!!}
  sound ._ ._ +-assoc x = {!!}
  sound ._ ._ +-assoc' x = {!!}
  sound ._ ._ refl-+ x = {!!}
  sound ._ ._ (cong-+ s s₁) x = {!!}
  sound ._ ._ (cong-lproj s) x = {!!}
  sound ._ ._ (cong-rproj s) x = {!!}
  sound ._ ._ (cong-app s) x = {!!}
  sound ._ ._ (cong-rec s) x = {!!}
  sound ._ ._ lam-s x = {!!}
  sound e ._ l-proj-s x = {!!}
  sound e ._ r-proj-s x = {!!}
  sound ._ ._ rec-steps-s x = {!!}
  sound e ._ rec-steps-z x = {!!}

{-

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

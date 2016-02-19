{- INTERPRETATION OF NEW COMPLEXITY LANGUAGE -}

{-# OPTIONS --no-termination-check #-}

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
  [ list τ ]t = (List (fst [ τ ]t)) , list-p (snd [ τ ]t)
  [ bool ]t = Bool , bool-p
  [ C ]t = Nat , nat-p
  [ rnat ]t = Nat , nat-p

  [_]tm : ∀ {A} → CTpM A → Preorder-max-str (snd [ A ]t)
  [ runit ]tm = unit-pM
  [ rn ]tm = nat-pM
  [ e ×cm e₁ ]tm = axb-pM [ e ]tm [ e₁ ]tm
  [ _->cm_ {τ1} e ]tm = mono-pM [ e ]tm
  
  -- interpret contexts as preorders
  [_]c : Ctx → PREORDER
  [ [] ]c = unit-p
  [ τ :: Γ ]c = [ Γ ]c ×p [ τ ]t

  lookup : ∀{Γ τ} → τ ∈ Γ → el ([ Γ ]c ->p [ τ ]t)
  lookup (i0 {Γ} {τ}) = snd' id
  lookup (iS {Γ} {τ} {τ1} x) = comp (fst' id) (lookup x)

  interpE : ∀{Γ τ} → Γ |- τ → el ([ Γ ]c ->p [ τ ]t)
  postulate
    sound : ∀ {Γ τ} (e e' : Γ |- τ) → e ≤s e' → PREORDER≤ ([ Γ ]c ->p [ τ ]t) (interpE e) (interpE e')
  interpE unit = monotone (λ x → <>) (λ x y x₁ → <>)
  interpE 0C = monotone (λ x → Z) (λ x y x₁ → <>)
  interpE 1C = monotone (λ x → S Z) (λ x y x₁ → <>)
  interpE (plusC e e₁) =
    monotone (λ x → Monotone.f (interpE e) x + Monotone.f (interpE e₁) x)
             (λ x y x₁ → plus-lem (Monotone.f (interpE e) x) (Monotone.f (interpE e₁) x) (Monotone.f (interpE e) y) (Monotone.f (interpE e₁) y)
               (Monotone.is-monotone (interpE e) x y x₁) (Monotone.is-monotone (interpE e₁) x y x₁))
  interpE (var x) = lookup x
  interpE z = monotone (λ x → Z) (λ x y x₁ → <>)
  interpE (s e) = monotone (λ x → S (Monotone.f (interpE e) x)) (λ x y x₁ → Monotone.is-monotone (interpE e) x y x₁)
  interpE {Γ} {τ} (rec e e₁ e₂) = comp (pair' id (interpE e)) (♭rec' (interpE e₁) (interpE e₂))
  interpE (lam e) = lam' (interpE e)
  interpE (app e e₁) = app' (interpE e) (interpE e₁)
  interpE rz = z'
  interpE (rsuc e) = suc' (interpE e)
  interpE (rrec e e₁ e₂ P) = comp (pair' id (interpE e)) (rec' (interpE e₁) (unlam' (unlam' (interpE e₂))) (λ x → sound e₁ (app (app e₂ rz) e₁) P x))
  interpE (prod e e₁) = pair' (interpE e) (interpE e₁)
  interpE (l-proj e) = fst' (interpE e)
  interpE (r-proj e) = snd' (interpE e)
  interpE nil = nil'
  interpE (e ::c e₁) = cons' (interpE e) (interpE e₁)
  interpE (listrec e e₁ e₂) = comp (pair' id (interpE e)) (lrec' (interpE e₁) (interpE e₂))
  interpE true = monotone (λ x → True) (λ x y x₁ → <>)
  interpE false = monotone (λ x → False) (λ x y x₁ → <>)
  interpE {Γ} {τ'} (max τ e1 e2) =
    monotone (λ x → Preorder-max-str.max [ τ ]tm (Monotone.f (interpE e1) x) (Monotone.f (interpE e2) x))
    (λ x y x₁ → Preorder-max-str.max-lub [ τ ]tm (Preorder-max-str.max [ τ ]tm (Monotone.f (interpE e1) y) (Monotone.f (interpE e2) y))
                (Monotone.f (interpE e1) x) (Monotone.f (interpE e2) x)
                (Preorder-str.trans (snd [ τ' ]t) (Monotone.f (interpE e1) x) (Monotone.f (interpE e1) y)
                (Preorder-max-str.max [ τ ]tm (Monotone.f (interpE e1) y) (Monotone.f (interpE e2) y))
                  (Monotone.is-monotone (interpE e1) x y x₁) (Preorder-max-str.max-l [ τ ]tm (Monotone.f (interpE e1) y) (Monotone.f (interpE e2) y)))
                (Preorder-str.trans (snd [ τ' ]t) (Monotone.f (interpE e2) x) (Monotone.f (interpE e2) y)
                (Preorder-max-str.max [ τ ]tm (Monotone.f (interpE e1) y) (Monotone.f (interpE e2) y))
                  (Monotone.is-monotone (interpE e2) x y x₁) (Preorder-max-str.max-r [ τ ]tm (Monotone.f (interpE e1) y) (Monotone.f (interpE e2) y))))

  throw-r : ∀ {Γ Γ' τ} → rctx Γ (τ :: Γ') → rctx Γ Γ'
  throw-r d = λ x → d (iS x)

  interpR : ∀ {Γ Γ'} → rctx Γ Γ' → MONOTONE [ Γ ]c [ Γ' ]c
  interpR {Γ' = []} ρ = monotone (λ _ → <>) (λ x y x₁ → <>)
  interpR {Γ' = τ :: Γ'} ρ = monotone (λ x → (Monotone.f (interpR (throw-r ρ)) x) , (Monotone.f (lookup (ρ i0)) x))
                             (λ x y x₁ → (Monotone.is-monotone (interpR (throw-r ρ)) x y x₁) , (Monotone.is-monotone (lookup (ρ i0)) x y x₁))

  throw-s : ∀ {Γ Γ' τ} → sctx Γ (τ :: Γ') → sctx Γ Γ'
  throw-s d = λ x → d (iS x)

  interpS : ∀ {Γ Γ'} → sctx Γ Γ' → el ([ Γ ]c ->p [ Γ' ]c)
  interpS {Γ' = []} Θ = monotone (λ _ → <>) (λ x y x₁ → <>)
  interpS {Γ' = τ :: Γ'} Θ = monotone (λ x → Monotone.f (interpS (throw-s Θ)) x , Monotone.f (interpE (Θ i0)) x)
                             (λ x y x₁ → Monotone.is-monotone (interpS (throw-s Θ)) x y x₁ , (Monotone.is-monotone (interpE (Θ i0)) x y x₁))

  rec-lem : ∀ {Γ τ} → (k : fst [ Γ ]c) (e0 e0' e1 e1' : fst [ τ ]t) (m : Nat)
          → (Preorder-str.≤ (snd [ τ ]t) e0 e0') → (Preorder-str.≤ (snd [ τ ]t) e1 e1')
          → (Preorder-str.≤ (snd [ τ ]t) (natrec e0 (λ n k → e1) m) (natrec e0' (λ n k → e1') m))
  rec-lem k e0 e0' e1 e1' Z p q = p
  rec-lem k e0 e0' e1 e1' (S m) p q = q

  ren-eq-l-lam : ∀ {Γ Γ' τ1} (ρ : rctx Γ Γ') (k : fst [ Γ ]c) (x : fst [ τ1 ]t)
               → Preorder-str.≤ (snd [ Γ' ]c) (Monotone.f (interpR (throw-r (r-extend {_} {_} {τ1} ρ))) (k , x)) (Monotone.f (interpR ρ) k)
  ren-eq-l-lam {Γ' = []} ρ k x = <>
  ren-eq-l-lam {Γ' = x :: Γ'} ρ k x₁ =
    (ren-eq-l-lam (throw-r ρ) k x₁) ,
    (Preorder-str.refl (snd [ x ]t) (Monotone.f (lookup (ρ i0)) k))

  ren-eq-l : ∀ {Γ Γ' τ} → (ρ : rctx Γ Γ') → (e : Γ' |- τ) → (k : fst [ Γ ]c)
           → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
  ren-eq-l ρ unit k = <>
  ren-eq-l ρ 0C k = <>
  ren-eq-l ρ 1C k = <>
  ren-eq-l ρ (plusC e e₁) k =
    plus-lem (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE (ren e₁ ρ)) k)
             (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))
               (ren-eq-l ρ e k) (ren-eq-l ρ e₁ k)
  ren-eq-l {τ = τ} ρ (var i0) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (lookup (ρ i0)) k)
  ren-eq-l {τ = τ} ρ (var (iS x)) k = ren-eq-l (throw-r ρ) (var x) k
  ren-eq-l ρ z k = <>
  ren-eq-l ρ (s e) k = ren-eq-l ρ e k
  ren-eq-l {Γ} {Γ'} {τ = τ} ρ (rec e e₁ e₂) k =
    Preorder-str.trans (snd [ τ ]t)
      (natrec (Monotone.f (interpE (ren e₁ ρ)) k) (λ n x₂ → Monotone.f (interpE (ren e₂ (r-extend (r-extend ρ)))) ((k , x₂) , n))
              (Monotone.f (interpE (ren e ρ)) k))
      (natrec (Monotone.f (interpE (ren e₁ ρ)) k) (λ n x₂ → Monotone.f (interpE (ren e₂ (r-extend (r-extend ρ)))) ((k , x₂) , n))
              (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
      (natrec (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k)) (λ n x₂ → Monotone.f (interpE e₂) ((Monotone.f (interpR ρ) k , x₂) , n))
              (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
        (♭h-fix-args (interpE (ren e₁ ρ)) (interpE (ren e₂ (r-extend (r-extend ρ))))
          (k , Monotone.f (interpE (ren e ρ)) k) (k , Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
          (ren-eq-l ρ e k))
        (rec-lem {Γ} k
           (Monotone.f {fst [ Γ ]c} {fst [ τ ]t} {snd [ Γ ]c} {snd [ τ ]t} (interpE {Γ} {τ} (ren e₁ ρ)) k)
           (Monotone.f {fst [ Γ' ]c} {fst [ τ ]t} {snd [ Γ' ]c} {snd [ τ ]t} (interpE {Γ'} {τ} e₁)
           (Monotone.f {fst [ Γ ]c} {fst [ Γ' ]c} {snd [ Γ ]c} {snd [ Γ' ]c} (interpR ρ) k))
           (λ n x₂ → Monotone.f {fst [ nat :: τ :: Γ ]c} {fst [ τ ]t} {snd [ nat :: τ :: Γ ]c} {snd [ τ ]t}
             (interpE {nat :: τ :: Γ} {τ} (ren e₂ (r-extend {τ :: Γ} {τ :: Γ'} (r-extend {Γ} {Γ'} ρ)))) ((k , x₂) , n))
           (λ n x₂ → Monotone.f {fst [ nat :: τ :: Γ' ]c} {fst [ τ ]t} {snd [ nat :: τ :: Γ' ]c} {snd [ τ ]t}
             (interpE {nat :: τ :: Γ'} {τ} e₂) ((Monotone.f {fst [ Γ ]c} {fst [ Γ' ]c} {snd [ Γ ]c} {snd [ Γ' ]c} (interpR {Γ} ρ) k , x₂) , n))
           (Monotone.f {fst [ Γ' ]c} {fst [ nat ]t} {snd [ Γ' ]c} {snd [ nat ]t} (interpE {Γ'} {nat} e) (Monotone.f {_} (interpR {Γ} ρ) k))
             (ren-eq-l {Γ} ρ e₁ k) {!!})
       {- (rec-lem k
          (Monotone.f (interpE (ren e₁ ρ)) k)
          (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))
          (λ n x₂ → Monotone.f (interpE (ren e₂ (r-extend (r-extend ρ)))) ((k , x₂) , n))
          (λ n x₂ → Monotone.f (interpE e₂) ((Monotone.f (interpR ρ) k , x₂) , n))
          (Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
            (ren-eq-l ρ e₁ k) {!!})-}
  ren-eq-l {Γ} {τ = τ1 ->c τ2} ρ (lam e) k x =
    Preorder-str.trans (snd [ τ2 ]t)
      (Monotone.f (Monotone.f (interpE (ren (lam e) ρ)) k) x)
      (Monotone.f (interpE e) (Monotone.f (interpR (r-extend {_} {_} {τ1} ρ)) (k , x)))
      (Monotone.f (interpE e) (Monotone.f (interpR ρ) k , x))
        (ren-eq-l (r-extend ρ) e (k , x))
        (Monotone.is-monotone (interpE e)
          (Monotone.f (interpR (r-extend {_} {_} {τ1} ρ)) (k , x))
          (Monotone.f (interpR ρ) k , x)
            (ren-eq-l-lam ρ k x ,
            (Preorder-str.refl (snd [ τ1 ]t) x)))
  ren-eq-l {Γ} {τ = τ} ρ (app e e₁) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE (ren e₁ ρ)) k))
      (Monotone.f (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k)))
      (Monotone.f (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k)))
        (Monotone.is-monotone (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE (ren e₁ ρ)) k) (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k)) (ren-eq-l ρ e₁ k))
        (ren-eq-l ρ e k (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k)))
  ren-eq-l ρ rz k = <>
  ren-eq-l ρ (rsuc e) k = ren-eq-l ρ e k
  ren-eq-l ρ (rrec e e₁ e₂ P) k = {!!}
  ren-eq-l ρ (prod e e₁) k = (ren-eq-l ρ e k) , (ren-eq-l ρ e₁ k)
  ren-eq-l ρ (l-proj e) k = fst (ren-eq-l ρ e k)
  ren-eq-l ρ (r-proj e) k = snd (ren-eq-l ρ e k)
  ren-eq-l ρ nil k = <>
  ren-eq-l ρ (e ::c e₁) k = (ren-eq-l ρ e k) , (ren-eq-l ρ e₁ k)
  ren-eq-l ρ (listrec e e₁ e₂) k = {!!}
  ren-eq-l ρ true k = <>
  ren-eq-l ρ false k = <>
  ren-eq-l {τ = τ} ρ (max x e e₁) k =
    Preorder-max-str.max-lub [ x ]tm
      (Monotone.f (interpE (max x e e₁)) (Monotone.f (interpR ρ) k))
      (Monotone.f (interpE (ren e ρ)) k)
      (Monotone.f (interpE (ren e₁ ρ)) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (ren e ρ)) k)
          (Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
          (Monotone.f (interpE (max x e e₁)) (Monotone.f (interpR ρ) k))
            (ren-eq-l ρ e k)
            (Preorder-max-str.max-l [ x ]tm (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))))
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (ren e₁ ρ)) k)
          (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))
          (Monotone.f (interpE (max x e e₁)) (Monotone.f (interpR ρ) k))
            (ren-eq-l ρ e₁ k)
            (Preorder-max-str.max-r [ x ]tm (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))))

  ren-eq-r-lam : ∀ {Γ Γ' τ1} (ρ : rctx Γ Γ') (k : fst [ Γ ]c) (x : fst [ τ1 ]t)
               → Preorder-str.≤ (snd [ Γ' ]c) (Monotone.f (interpR ρ) k) (Monotone.f (interpR (throw-r (r-extend {_} {_} {τ1} ρ))) (k , x))
  ren-eq-r-lam {Γ' = []} ρ k x = <>
  ren-eq-r-lam {Γ' = x :: Γ'} ρ k x₁ =
    (ren-eq-r-lam (throw-r ρ) k x₁) ,
    (Preorder-str.refl (snd [ x ]t) (Monotone.f (lookup (ρ i0)) k))

  ren-eq-r : ∀ {Γ Γ' τ} → (ρ : rctx Γ Γ') → (e : Γ' |- τ) → (k : fst [ Γ ]c)
           → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)) (Monotone.f (interpE (ren e ρ)) k)
  ren-eq-r ρ unit k = <>
  ren-eq-r ρ 0C k = <>
  ren-eq-r ρ 1C k = <>
  ren-eq-r ρ (plusC e e₁) k =
    plus-lem (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))
             (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE (ren e₁ ρ)) k)
               (ren-eq-r ρ e k) (ren-eq-r ρ e₁ k)
  ren-eq-r {τ = τ} ρ (var i0) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (lookup (ρ i0)) k)
  ren-eq-r {τ = τ} ρ (var (iS x)) k = ren-eq-r (throw-r ρ) (var x) k
  ren-eq-r ρ z k = <>
  ren-eq-r ρ (s e) k = ren-eq-r ρ e k
  ren-eq-r ρ (rec e e₁ e₂) k = {!!}
  ren-eq-r {Γ} {τ = τ1 ->c τ2} ρ (lam e) k x =
    Preorder-str.trans (snd [ τ2 ]t)
      (Monotone.f (interpE e) (Monotone.f (interpR ρ) k , x))
      (Monotone.f (interpE e) (Monotone.f (interpR (r-extend {_} {_} {τ1} ρ)) (k , x)))
      (Monotone.f (Monotone.f (interpE (ren (lam e) ρ)) k) x)
        ((Monotone.is-monotone (interpE e)
          (Monotone.f (interpR ρ) k , x)
          (Monotone.f (interpR (r-extend {_} {_} {τ1} ρ)) (k , x))
            (ren-eq-r-lam ρ k x ,
            (Preorder-str.refl (snd [ τ1 ]t) x))))
        (ren-eq-r (r-extend ρ) e (k , x))
  ren-eq-r {Γ} {τ = τ} ρ (app e e₁) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k)))
      (Monotone.f (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k)))
      (Monotone.f (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE (ren e₁ ρ)) k))
        (ren-eq-r ρ e k (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k)))
        (Monotone.is-monotone (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k)) (Monotone.f (interpE (ren e₁ ρ)) k) (ren-eq-r ρ e₁ k))
  ren-eq-r ρ rz k = <>
  ren-eq-r ρ (rsuc e) k = ren-eq-r ρ e k
  ren-eq-r ρ (rrec e e₁ e₂ P) k = {!!}
  ren-eq-r ρ (prod e e₁) k = (ren-eq-r ρ e k) , (ren-eq-r ρ e₁ k)
  ren-eq-r ρ (l-proj e) k = fst (ren-eq-r ρ e k)
  ren-eq-r ρ (r-proj e) k = snd (ren-eq-r ρ e k)
  ren-eq-r ρ nil k = <>
  ren-eq-r ρ (e ::c e₁) k = (ren-eq-r ρ e k) , (ren-eq-r ρ e₁ k)
  ren-eq-r ρ (listrec e e₁ e₂) k = {!!}
  ren-eq-r ρ true k = <>
  ren-eq-r ρ false k = <>
  ren-eq-r {τ = τ} ρ (max x e e₁) k =
    Preorder-max-str.max-lub [ x ]tm
      (Monotone.f (interpE (ren (max x e e₁) ρ)) k)
      (Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
      (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
          (Monotone.f (interpE (ren e ρ)) k)
          (Monotone.f (interpE (ren (max x e e₁) ρ)) k)
            (ren-eq-r ρ e k)
            (Preorder-max-str.max-l [ x ]tm (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE (ren e₁ ρ)) k)))
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))
          (Monotone.f (interpE (ren e₁ ρ)) k)
          (Monotone.f (interpE (ren (max x e e₁) ρ)) k)
            (ren-eq-r ρ e₁ k)
            (Preorder-max-str.max-r [ x ]tm (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE (ren e₁ ρ)) k)))

  ids-lem-l : ∀ {Γ} (k : fst [ Γ ]c) → Preorder-str.≤ (snd [ Γ ]c) (Monotone.f (interpR {Γ} {Γ} (λ x₂ → x₂)) k) k
  ids-lem-l {[]} k = <>
  ids-lem-l {x :: Γ} (k1 , k2) =
    (Preorder-str.trans (snd [ Γ ]c)
       (Monotone.f (interpR {x :: Γ} {Γ} (throw-r (λ x₂ → x₂))) (k1 , k2))
       (Monotone.f (interpR {Γ} {Γ} (λ x₂ → x₂)) k1)
       k1
         (ren-eq-l-lam {Γ} {Γ} (λ x₂ → x₂) k1 k2)
         (ids-lem-l {Γ} k1)) ,
    (Preorder-str.refl (snd [ x ]t) k2)

  subst-eq-l-lam : ∀ {Γ Γ' τ1} (Θ : sctx Γ Γ') (k : fst [ Γ ]c) (x : fst [ τ1 ]t)
               → Preorder-str.≤ (snd [ Γ' ]c) (Monotone.f (interpS (throw-s (s-extend {_} {_} {τ1} Θ))) (k , x)) (Monotone.f (interpS Θ) k)
  subst-eq-l-lam {Γ' = []} Θ k x = <>
  subst-eq-l-lam {Γ} {Γ' = x :: Γ'} {τ1} Θ k x₁ =
    (subst-eq-l-lam (throw-s Θ) k x₁) ,
    Preorder-str.trans (snd [ x ]t)
      (Monotone.f (interpE (ren (Θ i0) iS)) (k , x₁))
      (Monotone.f (interpE (Θ i0)) (Monotone.f (interpR {τ1 :: Γ} {Γ} iS) (k , x₁)))
      (snd (Monotone.f (interpS Θ) k))
        (ren-eq-l iS (Θ i0) (k , x₁))
        (Monotone.is-monotone (interpE (Θ i0)) (Monotone.f (interpR {τ1 :: Γ} {Γ} iS) (k , x₁)) k
          (Preorder-str.trans (snd [ Γ ]c)
            (Monotone.f (interpR {τ1 :: Γ} {Γ} iS) (k , x₁))
            (Monotone.f (interpR {Γ} {Γ} (λ x₂ → x₂)) k)
            k
              (ren-eq-l-lam {Γ} {Γ} (λ x₂ → x₂) k x₁)
              (ids-lem-l {Γ} k)))

  subst-eq-l : ∀ {Γ Γ' τ} → (Θ : sctx Γ Γ') → (e : Γ' |- τ) → (k : fst [ Γ ]c)
             → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
  subst-eq-l Θ unit k = <>
  subst-eq-l Θ 0C k = <>
  subst-eq-l Θ 1C k = <>
  subst-eq-l Θ (plusC e e₁) k =
    plus-lem (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE (subst e₁ Θ)) k)
             (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k))
               (subst-eq-l Θ e k) (subst-eq-l Θ e₁ k)
  subst-eq-l {τ = τ} Θ (var i0) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE (Θ i0)) k)
  subst-eq-l {τ = τ} Θ (var (iS x)) k = subst-eq-l (throw-s Θ) (var x) k
  subst-eq-l Θ z k = <>
  subst-eq-l Θ (s e) k = subst-eq-l Θ e k
  subst-eq-l Θ (rec e e₁ e₂) k = {!!}
  subst-eq-l {Γ} {τ = τ1 ->c τ2} Θ (lam e) k x =
    Preorder-str.trans (snd [ τ2 ]t)
      (Monotone.f (Monotone.f (interpE (subst (lam e) Θ)) k) x)
      (Monotone.f (interpE e) (Monotone.f (interpS (s-extend {_} {_} {τ1} Θ)) (k , x)))
      (Monotone.f (interpE e) (Monotone.f (interpS Θ) k , x))
        (subst-eq-l (s-extend Θ) e (k , x))
        (Monotone.is-monotone (interpE e)
          (Monotone.f (interpS (s-extend {_} {_} {τ1} Θ)) (k , x))
          (Monotone.f (interpS Θ) k , x)
            (subst-eq-l-lam Θ k x , 
            (Preorder-str.refl (snd [ τ1 ]t) x)))
  subst-eq-l {Γ} {τ = τ} Θ (app e e₁) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE (subst e₁ Θ)) k))
      (Monotone.f (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k)))
      (Monotone.f (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k)))
        (Monotone.is-monotone (Monotone.f (interpE (subst e Θ)) k)
          (Monotone.f (interpE (subst e₁ Θ)) k) (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k)) (subst-eq-l Θ e₁ k))
        (subst-eq-l Θ e k (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k)))
  subst-eq-l Θ rz k = <>
  subst-eq-l Θ (rsuc e) k = subst-eq-l Θ e k
  subst-eq-l Θ (rrec e e₁ e₂ P) k = {!!}
  subst-eq-l Θ (prod e e₁) k = (subst-eq-l Θ e k) , (subst-eq-l Θ e₁ k)
  subst-eq-l Θ (l-proj e) k = fst (subst-eq-l Θ e k)
  subst-eq-l Θ (r-proj e) k = snd (subst-eq-l Θ e k)
  subst-eq-l Θ nil k = <>
  subst-eq-l Θ (e ::c e₁) k = (subst-eq-l Θ e k) , (subst-eq-l Θ e₁ k)
  subst-eq-l Θ (listrec e e₁ e₂) k = {!!}
  subst-eq-l Θ true k = <>
  subst-eq-l Θ false k = <>
  subst-eq-l {τ = τ} Θ (max x e e₁) k =
    Preorder-max-str.max-lub [ x ]tm
      (Monotone.f (interpE (max x e e₁)) (Monotone.f (interpS Θ) k))
      (Monotone.f (interpE (subst e Θ)) k)
      (Monotone.f (interpE (subst e₁ Θ)) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e Θ)) k)
          (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
          (Monotone.f (interpE (max x e e₁)) (Monotone.f (interpS Θ) k))
            (subst-eq-l Θ e k)
            (Preorder-max-str.max-l [ x ]tm (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k))))
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e₁ Θ)) k)
          (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k))
          (Monotone.f (interpE (max x e e₁)) (Monotone.f (interpS Θ) k))
            (subst-eq-l Θ e₁ k)
            (Preorder-max-str.max-r [ x ]tm (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k))))

  ids-lem-r : ∀ {Γ} (k : fst [ Γ ]c) → Preorder-str.≤ (snd [ Γ ]c) k (Monotone.f (interpR {Γ} {Γ} (λ x₂ → x₂)) k)
  ids-lem-r {[]} k = <>
  ids-lem-r {x :: Γ} (k1 , k2) =
    (Preorder-str.trans (snd [ Γ ]c)
       k1
       (Monotone.f (interpR {Γ} {Γ} (λ x₂ → x₂)) k1)
       (Monotone.f (interpR {x :: Γ} {Γ} (throw-r (λ x₂ → x₂))) (k1 , k2))
         (ids-lem-r {Γ} k1)
         (ren-eq-r-lam {Γ} {Γ} (λ x₂ → x₂) k1 k2)) ,
    (Preorder-str.refl (snd [ x ]t) k2)

  subst-eq-r-lam : ∀ {Γ Γ' τ1} (Θ : sctx Γ Γ') (k : fst [ Γ ]c) (x : fst [ τ1 ]t)
               → Preorder-str.≤ (snd [ Γ' ]c) (Monotone.f (interpS Θ) k) (Monotone.f (interpS (throw-s (s-extend {_} {_} {τ1} Θ))) (k , x))
  subst-eq-r-lam {Γ' = []} Θ k x = <>
  subst-eq-r-lam {Γ} {Γ' = x :: Γ'} {τ1} Θ k x₁ =
    (subst-eq-r-lam (throw-s Θ) k x₁) ,
    Preorder-str.trans (snd [ x ]t)
      (snd (Monotone.f (interpS Θ) k))
      (Monotone.f (interpE (Θ i0)) (Monotone.f (interpR {τ1 :: Γ} {Γ} iS) (k , x₁)))
      (Monotone.f (interpE (ren (Θ i0) iS)) (k , x₁))
        (Monotone.is-monotone (interpE (Θ i0))
          k
          (Monotone.f (interpR {τ1 :: Γ} {Γ} iS) (k , x₁))
            (Preorder-str.trans (snd [ Γ ]c)
              k
              (Monotone.f (interpR {Γ} {Γ} (λ x₂ → x₂)) k)
              (Monotone.f (interpR {τ1 :: Γ} {Γ} iS) (k , x₁))
                (ids-lem-r {Γ} k)
                (ren-eq-r-lam {Γ} {Γ} (λ x₂ → x₂) k x₁)))
        (ren-eq-r iS (Θ i0) (k , x₁))

  subst-eq-r : ∀ {Γ Γ' τ} → (Θ : sctx Γ Γ') → (e : Γ' |- τ) → (k : fst [ Γ ]c)
             → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)) (Monotone.f (interpE (subst e Θ)) k)
  subst-eq-r Θ unit k = <>
  subst-eq-r Θ 0C k = <>
  subst-eq-r Θ 1C k = <>
  subst-eq-r Θ (plusC e e₁) k =
    plus-lem (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k))
             (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE (subst e₁ Θ)) k)
               (subst-eq-r Θ e k) (subst-eq-r Θ e₁ k)
  subst-eq-r {τ = τ} Θ (var i0) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE (Θ i0)) k)
  subst-eq-r {τ = τ} Θ (var (iS x)) k = subst-eq-r (throw-s Θ) (var x) k
  subst-eq-r Θ z k = <>
  subst-eq-r Θ (s e) k = subst-eq-r Θ e k
  subst-eq-r Θ (rec e e₁ e₂) k = {!!}
  subst-eq-r {Γ} {τ = τ1 ->c τ2} Θ (lam e) k x =
    Preorder-str.trans (snd [ τ2 ]t)
      (Monotone.f (interpE e) (Monotone.f (interpS Θ) k , x))
      (Monotone.f (interpE e) (Monotone.f (interpS (s-extend {_} {_} {τ1} Θ)) (k , x)))
      (Monotone.f (Monotone.f (interpE (subst (lam e) Θ)) k) x)
        ((Monotone.is-monotone (interpE e)
          (Monotone.f (interpS Θ) k , x)
          (Monotone.f (interpS (s-extend {_} {_} {τ1} Θ)) (k , x))
            (subst-eq-r-lam Θ k x ,
            (Preorder-str.refl (snd [ τ1 ]t) x))))
        (subst-eq-r (s-extend Θ) e (k , x))
  subst-eq-r {Γ} {τ = τ} Θ (app e e₁) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)) (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k)))
      (Monotone.f (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k)))
      (Monotone.f (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE (subst e₁ Θ)) k))
        (subst-eq-r Θ e k (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k)))
        (Monotone.is-monotone (Monotone.f (interpE (subst e Θ)) k)
          (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k)) (Monotone.f (interpE (subst e₁ Θ)) k) (subst-eq-r Θ e₁ k))
  subst-eq-r Θ rz k = <>
  subst-eq-r Θ (rsuc e) k = subst-eq-r Θ e k
  subst-eq-r Θ (rrec e e₁ e₂ P) k = {!!}
  subst-eq-r Θ (prod e e₁) k = (subst-eq-r Θ e k) , (subst-eq-r Θ e₁ k)
  subst-eq-r Θ (l-proj e) k = fst (subst-eq-r Θ e k)
  subst-eq-r Θ (r-proj e) k = snd (subst-eq-r Θ e k)
  subst-eq-r Θ nil k = <>
  subst-eq-r Θ (e ::c e₁) k = (subst-eq-r Θ e k) , (subst-eq-r Θ e₁ k)
  subst-eq-r Θ (listrec e e₁ e₂) k = {!!}
  subst-eq-r Θ true k = <>
  subst-eq-r Θ false k = <>
  subst-eq-r {τ = τ} Θ (max x e e₁) k =
    Preorder-max-str.max-lub [ x ]tm
      (Monotone.f (interpE (subst (max x e e₁) Θ)) k)
      (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
      (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k))
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
          (Monotone.f (interpE (subst e Θ)) k)
          (Monotone.f (interpE (subst (max x e e₁) Θ)) k)
            (subst-eq-r Θ e k)
            (Preorder-max-str.max-l [ x ]tm (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE (subst e₁ Θ)) k)))
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k))
          (Monotone.f (interpE (subst e₁ Θ)) k)
          (Monotone.f (interpE (subst (max x e e₁) Θ)) k)
            (subst-eq-r Θ e₁ k)
            (Preorder-max-str.max-r [ x ]tm (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE (subst e₁ Θ)) k)))

{-
  mutual
    subst-id-abs : ∀ {Γ τ ρ} → (e : ρ :: Γ |- τ) → (k : fst [ Γ ]c) → (p₁ : fst [ ρ ]t)
                 → Monotone.f (interpE e) (k , p₁) == Monotone.f (interpE (subst e (s-extend var))) (k , p₁)
    subst-id-abs e k p₁ = Monotone.f (interpE e) (k , p₁) =⟨ subst-id-lem e (k , p₁) ⟩
                          Monotone.f (interpE (subst e ids)) (k , p₁) =⟨ ap2 Monotone.f (ap interpE (ap (subst e) extend-id-once)) Refl ⟩
                          (Monotone.f (interpE (subst e (s-extend var))) (k , p₁) ∎)

    subst-id-rec : ∀ {Γ τ} → (e₂ : nat :: τ :: Γ |- τ) → (k : fst [ Γ ]c) → (n : Nat) → (x₂ : fst [ τ ]t)
                 → Monotone.f (interpE e₂) ((k , x₂) , n) == Monotone.f (interpE (subst e₂ (s-extend (s-extend ids)))) ((k , x₂) , n)
    subst-id-rec e₂ k n x₂ = Monotone.f (interpE e₂) ((k , x₂) , n) =⟨ subst-id-lem e₂ ((k , x₂) , n) ⟩
                             Monotone.f (interpE (subst e₂ ids)) ((k , x₂) , n) =⟨ ap2 Monotone.f (ap interpE (ap (subst e₂) extend-id-twice)) Refl ⟩
                             (Monotone.f (interpE (subst e₂ (s-extend (s-extend ids)))) ((k , x₂) , n) ∎)

    subst-id-lrec : ∀ {Γ τ τ1} → (e₂ : τ1 :: list τ1 :: τ :: Γ |- τ) → (k : fst [ Γ ]c) → (h : fst [ τ1 ]t) → (t : List (fst [ τ1 ]t)) → (x₃ : fst [ τ ]t)
                  → Monotone.f (interpE e₂) (((k , x₃) , t) , h) == Monotone.f (interpE (subst e₂ (s-extend (s-extend (s-extend ids))))) (((k , x₃) , t) , h)
    subst-id-lrec e₂ k h t x₃ = Monotone.f (interpE e₂) (((k , x₃) , t) , h) =⟨ subst-id-lem e₂ (((k , x₃) , t) , h) ⟩
                                Monotone.f (interpE (subst e₂ ids)) (((k , x₃) , t) , h) =⟨ ap2 Monotone.f (ap interpE (ap (subst e₂) extend-id-thrice)) Refl ⟩
                                (Monotone.f (interpE (subst e₂ (s-extend (s-extend (s-extend ids))))) (((k , x₃) , t) , h) ∎)
-}

  s-id-l : ∀ {Γ τ} → (e : Γ |- τ) → (k : fst [ Γ ]c) → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE e) k) (Monotone.f (interpE (subst e ids)) k)
  s-id-l unit k = <>
  s-id-l 0C k = <>
  s-id-l 1C k = <>
  s-id-l (plusC e e₁) k =
    plus-lem (Monotone.f (interpE e) k) (Monotone.f (interpE e₁) k)
    (Monotone.f (interpE (subst e (λ x → var x))) k) (Monotone.f (interpE (subst e₁ (λ x → var x))) k)
      (s-id-l e k) (s-id-l e₁ k)
  s-id-l {_} {τ} (var x) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (lookup x) k)
  s-id-l z k = <>
  s-id-l (s e) k = s-id-l e k
  s-id-l {Γ} {τ} (rec e e₁ e₂) k =
    Preorder-str.trans (snd [ τ ]t)
      (natrec (Monotone.f (interpE e₁) k) (λ n x₂ → Monotone.f (interpE e₂) ((k , x₂) , n))
              (Monotone.f (interpE e) k))
      (natrec (Monotone.f (interpE e₁) k) (λ n x₂ → Monotone.f (interpE e₂) ((k , x₂) , n))
              (Monotone.f (interpE (subst e ids)) k))
      (natrec (Monotone.f (interpE (subst e₁ ids)) k) (λ n x₂ → Monotone.f (interpE (subst e₂ (s-extend (s-extend ids)))) ((k , x₂) , n))
              (Monotone.f (interpE (subst e ids)) k))
        (♭h-fix-args (interpE e₁) (interpE e₂) (k , (Monotone.f (interpE e) k)) (k , Monotone.f (interpE (subst e ids)) k) (s-id-l e k))
        (♭h-smash
          (interpE e₁)
          (interpE (subst e₁ ids))
          (interpE e₂)
          (interpE (subst e₂ (s-extend {_} {_} {nat} (s-extend {_} {_} {τ} ids))))
          (k , Monotone.f {_} {_} {snd [ Γ ]c} {snd [ nat ]t} (interpE (subst e ids)) k)
          (s-id-l e₁ k) (λ n → {!λ x₂ → s-id-l e₂ ((k , x₂) , n)!}))
        {-(rec-lem {Γ} {_} k (Monotone.f {_} {_} {snd [ Γ ]c} {snd [ τ ]t} (interpE {_} {τ} e₁) k) (Monotone.f {_} {_} {snd [ Γ ]c} {snd [ τ ]t} (interpE (subst e₁ ids)) k)
                   (λ n x₂ → Monotone.f {_} {_} {snd [ nat :: τ :: Γ ]c} {snd [ τ ]t} (interpE e₂) ((k , x₂) , n))
                   (λ n x₂ → Monotone.f {_} {_} {snd [ nat :: τ :: Γ ]c} {snd [ τ ]t} (interpE (subst e₂ (s-extend {_} {_} {nat} (s-extend {_} {_} {τ} ids)))) ((k , x₂) , n))
                   (Monotone.f {_} {_} {snd [ Γ ]c} {snd [ nat ]t} (interpE (subst e ids)) k)
                   (s-id-l e₁ k) (λ n x₂ → s-id-l e₂ ((k , x₂) , n)))-}
{-    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (rec e e₁ e₂)) k)
      (Monotone.f (interpE (rec e e₁ e₂)) (Monotone.f (interpS {Γ} {_} ids) k))
      (Monotone.f (interpE (subst (rec e e₁ e₂) ids)) k)
        {!!}
        --(Monotone.is-monotone (interpE (rec e e₁ e₂)) k (Monotone.f (interpS {Γ} {_} ids) k) {!!})
        (subst-eq-r ids (rec e e₁ e₂) k)-}
  s-id-l {Γ} {ρ ->c τ} (lam e) k x =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE e) (k , x))
      (Monotone.f (interpE (subst e ids)) (k , x))
      (Monotone.f (interpE (subst e (s-extend ids))) (k , x))
        (s-id-l e (k , x))
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e ids)) (k , x))
          (Monotone.f (interpE e) (Monotone.f (interpS {ρ :: Γ} {_} ids) (k , x)))
          (Monotone.f (interpE (subst e (s-extend ids))) (k , x))
            (subst-eq-l ids e (k , x))
            (subst-eq-r (s-extend ids) e (k , x)))
  s-id-l {_} {τ} (app e e₁) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (Monotone.f (interpE e) k) (Monotone.f (interpE e₁) k))
      (Monotone.f (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE e₁) k))
      (Monotone.f (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE (subst e₁ ids)) k))
        (s-id-l e k (Monotone.f (interpE e₁) k))
        (Monotone.is-monotone (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE e₁) k) (Monotone.f (interpE (subst e₁ ids)) k) (s-id-l e₁ k))
  s-id-l rz k = <>
  s-id-l (rsuc e) k = s-id-l e k
  s-id-l (rrec e e₁ e₂ P) k = {!!}
  s-id-l (prod e e₁) k = (s-id-l e k) , (s-id-l e₁ k)
  s-id-l (l-proj e) k = fst (s-id-l e k)
  s-id-l (r-proj e) k = snd (s-id-l e k)
  s-id-l nil k = <>
  s-id-l (e ::c e₁) k = s-id-l e k , s-id-l e₁ k
  s-id-l (listrec e e₁ e₂) k = {!!}
  s-id-l true k = <>
  s-id-l false k = <>
  s-id-l {_} {τ} (max x e e₁) k =
    Preorder-max-str.max-lub [ x ]tm
      (Preorder-max-str.max [ x ]tm (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE (subst e₁ ids)) k))
      (Monotone.f (interpE e) k)
      (Monotone.f (interpE e₁) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE e) k)
          (Monotone.f (interpE (subst e ids)) k)
          (Preorder-max-str.max [ x ]tm (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE (subst e₁ ids)) k))
            (s-id-l e k) (Preorder-max-str.max-l [ x ]tm (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE (subst e₁ ids)) k)))
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE e₁) k)
          (Monotone.f (interpE (subst e₁ ids)) k)
          (Preorder-max-str.max [ x ]tm (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE (subst e₁ ids)) k))
            (s-id-l e₁ k) (Preorder-max-str.max-r [ x ]tm (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE (subst e₁ ids)) k)))

  s-id-r : ∀ {Γ τ} → (e : Γ |- τ) → (k : fst [ Γ ]c) → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE e) k)
  s-id-r unit k = <>
  s-id-r 0C k = <>
  s-id-r 1C k = <>
  s-id-r (plusC e e₁) k =
    plus-lem (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE (subst e₁ ids)) k)
    (Monotone.f (interpE e) k) (Monotone.f (interpE e₁) k)
      (s-id-r e k) (s-id-r e₁ k)
  s-id-r {τ = τ} (var x) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (lookup x) k)
  s-id-r z k = <>
  s-id-r (s e) k = (s-id-r e k)
  s-id-r {Γ} {τ} (rec e e₁ e₂) k = {!!}
  s-id-r {Γ} {τ = τ1 ->c τ2} (lam e) k x =
    Preorder-str.trans (snd [ τ2 ]t)
      (Monotone.f (interpE (subst e (s-extend ids))) (k , x))
      (Monotone.f (interpE (subst e ids)) (k , x))
      (Monotone.f (interpE e) (k , x))
        (Preorder-str.trans (snd [ τ2 ]t)
          (Monotone.f (interpE (subst e (s-extend ids))) (k , x))
          (Monotone.f (interpE e) (Monotone.f (interpS {τ1 :: Γ} {_} ids) (k , x)))
          (Monotone.f (interpE (subst e ids)) (k , x))
            (subst-eq-l (s-extend ids) e (k , x))
            (subst-eq-r ids e (k , x)))
        (s-id-r e (k , x))
  s-id-r {τ = τ} (app e e₁) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE (subst e₁ ids)) k))
      (Monotone.f (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE e₁) k))
      (Monotone.f (Monotone.f (interpE e) k) (Monotone.f (interpE e₁) k))
        (Monotone.is-monotone (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE (subst e₁ ids)) k) (Monotone.f (interpE e₁) k) (s-id-r e₁ k))
        (s-id-r e k (Monotone.f (interpE e₁) k))
  s-id-r rz k = <>
  s-id-r (rsuc e) k = (s-id-r e k)
  s-id-r (rrec e e₁ e₂ P) k = {!!}
  s-id-r (prod e e₁) k = s-id-r e k , s-id-r e₁ k
  s-id-r (l-proj e) k = fst (s-id-r e k)
  s-id-r (r-proj e) k = snd (s-id-r e k)
  s-id-r nil k = <>
  s-id-r (e ::c e₁) k = s-id-r e k , s-id-r e₁ k
  s-id-r (listrec e e₁ e₂) k = {!!}
  s-id-r true k = <>
  s-id-r false k = <>
  s-id-r {τ = τ} (max x e e₁) k =
    Preorder-max-str.max-lub [ x ]tm
      (Preorder-max-str.max [ x ]tm (Monotone.f (interpE e) k) (Monotone.f (interpE e₁) k))
      (Monotone.f (interpE (subst e ids)) k)
      (Monotone.f (interpE (subst e₁ ids)) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e ids)) k)
          (Monotone.f (interpE e) k)
          (Preorder-max-str.max [ x ]tm (Monotone.f (interpE e) k) (Monotone.f (interpE e₁) k))
            (s-id-r e k) (Preorder-max-str.max-l [ x ]tm (Monotone.f (interpE e) k) (Monotone.f (interpE e₁) k)))
        (Preorder-str.trans (snd [ τ ]t)
           (Monotone.f (interpE (subst e₁ ids)) k)
           (Monotone.f (interpE e₁) k)
           (Preorder-max-str.max [ x ]tm (Monotone.f (interpE e) k) (Monotone.f (interpE e₁) k))
             (s-id-r e₁ k) (Preorder-max-str.max-r [ x ]tm (Monotone.f (interpE e) k) (Monotone.f (interpE e₁) k)))

  s-rr-l : ∀ {Γ Γ' Γ'' τ} → (e : Γ'' |- τ) (ρ1 : rctx Γ Γ') (ρ2 : rctx Γ' Γ'') → (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (ren (ren e ρ2) ρ1)) k) (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k)
  s-rr-l unit ρ1 ρ2 k = <>
  s-rr-l 0C ρ1 ρ2 k = <>
  s-rr-l 1C ρ1 ρ2 k = <>
  s-rr-l (plusC e e₁) ρ1 ρ2 k =
    plus-lem (Monotone.f (interpE (ren (ren e ρ2) ρ1)) k) (Monotone.f (interpE (ren (ren e₁ ρ2) ρ1)) k)
    (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k) (Monotone.f (interpE (ren e₁ (ρ1 ∙rr ρ2))) k)
      (s-rr-l e ρ1 ρ2 k) (s-rr-l e₁ ρ1 ρ2 k)
  s-rr-l {τ = τ} (var x) ρ1 ρ2 k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (lookup (ρ1 (ρ2 x))) k)
  s-rr-l z ρ1 ρ2 k = <>
  s-rr-l (s e) ρ1 ρ2 k = s-rr-l e ρ1 ρ2 k
  s-rr-l (rec e e₁ e₂) ρ1 ρ2 k = {!!}
  s-rr-l {τ = τ1 ->c τ2} (lam e) ρ1 ρ2 k x =
    Preorder-str.trans (snd [ τ2 ]t)
      (Monotone.f (Monotone.f (interpE (ren (ren (lam e) ρ2) ρ1)) k) x)
      (Monotone.f (interpE (ren e (r-extend ρ1 ∙rr r-extend ρ2))) (k , x))
      (Monotone.f (interpE (ren e (r-extend (λ x₁ → ρ1 (ρ2 x₁))))) (k , x))
        (s-rr-l e (r-extend ρ1) (r-extend ρ2) (k , x))
        (Preorder-str.trans (snd [ τ2 ]t)
          (Monotone.f (interpE (ren e (r-extend ρ1 ∙rr r-extend ρ2))) (k , x))
          (Monotone.f (interpE e) (Monotone.f (interpR (r-extend {_} {_} {τ1} ρ1 ∙rr r-extend ρ2)) (k , x)))
          (Monotone.f (interpE (ren e (r-extend (λ x₁ → ρ1 (ρ2 x₁))))) (k , x))
            (ren-eq-l (r-extend ρ1 ∙rr r-extend ρ2) e (k , x))
            (ren-eq-r (r-extend (ρ1 ∙rr ρ2)) e (k , x)))
  s-rr-l {τ = τ} (app e e₁) ρ1 ρ2 k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (Monotone.f (interpE (ren (ren e ρ2) ρ1)) k) (Monotone.f (interpE (ren (ren e₁ ρ2) ρ1)) k))
      (Monotone.f (Monotone.f (interpE (ren e (λ x → ρ1 (ρ2 x)))) k) (Monotone.f (interpE (ren (ren e₁ ρ2) ρ1)) k))
      (Monotone.f (Monotone.f (interpE (ren e (λ x → ρ1 (ρ2 x)))) k) (Monotone.f (interpE (ren e₁ (λ x → ρ1 (ρ2 x)))) k))
        (s-rr-l e ρ1 ρ2 k (Monotone.f (interpE (ren (ren e₁ ρ2) ρ1)) k))
        (Monotone.is-monotone (Monotone.f (interpE (ren e (λ x → ρ1 (ρ2 x)))) k)
          (Monotone.f (interpE (ren (ren e₁ ρ2) ρ1)) k)
          (Monotone.f (interpE (ren e₁ (λ x → ρ1 (ρ2 x)))) k)
            (s-rr-l e₁ ρ1 ρ2 k))
  s-rr-l rz ρ1 ρ2 k = <>
  s-rr-l (rsuc e) ρ1 ρ2 k = s-rr-l e ρ1 ρ2 k
  s-rr-l (rrec e e₁ e₂ P) ρ1 ρ2 k = {!!}
  s-rr-l (prod e e₁) ρ1 ρ2 k = s-rr-l e ρ1 ρ2 k , s-rr-l e₁ ρ1 ρ2 k
  s-rr-l (l-proj e) ρ1 ρ2 k = fst (s-rr-l e ρ1 ρ2 k)
  s-rr-l (r-proj e) ρ1 ρ2 k = snd (s-rr-l e ρ1 ρ2 k)
  s-rr-l nil ρ1 ρ2 k = <>
  s-rr-l (e ::c e₁) ρ1 ρ2 k = s-rr-l e ρ1 ρ2 k , s-rr-l e₁ ρ1 ρ2 k
  s-rr-l (listrec e e₁ e₂) ρ1 ρ2 k = {!!}
  s-rr-l true ρ1 ρ2 k = <>
  s-rr-l false ρ1 ρ2 k = <>
  s-rr-l {τ = τ} (max x e e₁) ρ1 ρ2 k =
    Preorder-max-str.max-lub [ x ]tm
      (Preorder-max-str.max [ x ]tm (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k) (Monotone.f (interpE (ren e₁ (ρ1 ∙rr ρ2))) k))
      (Monotone.f (interpE (ren (ren e ρ2) ρ1)) k)
      (Monotone.f (interpE (ren (ren e₁ ρ2) ρ1)) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (ren (ren e ρ2) ρ1)) k)
          (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k)
          (Preorder-max-str.max [ x ]tm (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k) (Monotone.f (interpE (ren e₁ (ρ1 ∙rr ρ2))) k))
            (s-rr-l e ρ1 ρ2 k) (Preorder-max-str.max-l [ x ]tm (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k) (Monotone.f (interpE (ren e₁ (ρ1 ∙rr ρ2))) k)))
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (ren (ren e₁ ρ2) ρ1)) k)
          (Monotone.f (interpE (ren e₁ (ρ1 ∙rr ρ2))) k)
          (Preorder-max-str.max [ x ]tm (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k) (Monotone.f (interpE (ren e₁ (ρ1 ∙rr ρ2))) k))
            (s-rr-l e₁ ρ1 ρ2 k) (Preorder-max-str.max-r [ x ]tm (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k) (Monotone.f (interpE (ren e₁ (ρ1 ∙rr ρ2))) k)))
  s-rr-r : ∀ {Γ Γ' Γ'' τ} → (e : Γ'' |- τ) (ρ1 : rctx Γ Γ') (ρ2 : rctx Γ' Γ'') → (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k) (Monotone.f (interpE (ren (ren e ρ2) ρ1)) k)
  s-rr-r e ρ1 ρ2 k = {!!}

  s-rs-l : ∀ {Γ A B τ} (ρ : rctx Γ A) (Θ : sctx A B) (e : B |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (ren (subst e Θ) ρ)) k) (Monotone.f (interpE (subst e (ρ rs Θ))) k)
  s-rs-l ρ Θ e k = {!!}
  s-rs-r : ∀ {Γ A B τ} (ρ : rctx Γ A) (Θ : sctx A B) (e : B |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e (ρ rs Θ))) k) (Monotone.f (interpE (ren (subst e Θ) ρ)) k)
  s-rs-r ρ Θ e k = {!!}

  s-sr-l : ∀ {Γ Γ' Γ'' τ} (Θ : sctx Γ Γ') (ρ : rctx Γ' Γ'') (e : Γ'' |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst (ren e ρ) Θ)) k) (Monotone.f (interpE (subst e (Θ sr ρ))) k)
  s-sr-l Θ ρ e k = {!!}
  s-sr-r : ∀ {Γ Γ' Γ'' τ} (Θ : sctx Γ Γ') (ρ : rctx Γ' Γ'') (e : Γ'' |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e (Θ sr ρ))) k) (Monotone.f (interpE (subst (ren e ρ) Θ)) k)
  s-sr-r Θ ρ e k = {!!}

  s-ss-l : ∀ {Γ B C τ} (Θ1 : sctx Γ B) (Θ2 : sctx B C) (e : C |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e (Θ1 ss Θ2))) k) (Monotone.f (interpE (subst (subst e Θ2) Θ1)) k)
  s-ss-l Θ1 Θ2 e k = {!!}
  s-ss-r : ∀ {Γ B C τ} (Θ1 : sctx Γ B) (Θ2 : sctx B C) (e : C |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst (subst e Θ2) Θ1)) k) (Monotone.f (interpE (subst e (Θ1 ss Θ2))) k)
  s-ss-r Θ1 Θ2 e k = {!!}

  s-comp-l-lem-lem : ∀ {Γ Γ' τ1} (x : CTp) (Θ : sctx Γ (x :: Γ')) (v : Γ |- τ1) (k : fst [ Γ ]c)
                   → Preorder-str.≤ (snd [ Γ' ]c)
                       (Monotone.f (interpS (λ x₁ → subst (ren (Θ (iS x₁)) iS) (lem3' var v))) k)
                       (Monotone.f (interpS (λ x₁ → Θ (iS x₁))) k)
  s-comp-l-lem-lem {Γ' = []} x Θ v k = <>
  s-comp-l-lem-lem {Γ' = x :: Γ'} x₁ Θ v k =
    (s-comp-l-lem-lem x (throw-s Θ) v k) ,
    Preorder-str.trans (snd [ x ]t)
      (Monotone.f (interpE (subst (ren (Θ (iS i0)) iS) (lem3' var v))) k)
      (Monotone.f (interpE (subst (Θ (iS i0)) (q v sr iS))) k)
      (Monotone.f (interpE (Θ (iS i0))) k)
        (s-sr-l (q v) iS (Θ (iS i0)) k)
        (s-id-r (Θ (iS i0)) k)

  s-comp-l-lem : ∀ {Γ Γ' τ1} (Θ : sctx Γ Γ') (v : Γ |- τ1) (k : fst [ Γ ]c)
               → Preorder-str.≤ (snd [ Γ' ]c)
                   (Monotone.f (interpS (λ x → subst (ren (Θ x) iS) (lem3' ids v))) k)
                   (Monotone.f (interpS (λ x → Θ x)) k)
  s-comp-l-lem {Γ' = []} Θ v k = <>
  s-comp-l-lem {Γ' = x :: Γ'} Θ v k = 
    s-comp-l-lem-lem x Θ v k ,
    Preorder-str.trans (snd [ x ]t)
      (Monotone.f (interpE (subst (ren (Θ i0) iS) (lem3' var v))) k)
      (Monotone.f (interpE (subst (Θ i0) (q v sr iS))) k)
      (Monotone.f (interpE (Θ i0)) k)
        (s-sr-l (q v) iS (Θ i0) k)
        (s-id-r (Θ i0) k)

  s-comp-r-lem-lem : ∀ {Γ Γ' τ1} (x : CTp) (Θ : sctx Γ (x :: Γ')) (v : Γ |- τ1) (k : fst [ Γ ]c)
                   → Preorder-str.≤ (snd [ Γ' ]c)
                       (Monotone.f (interpS (λ x₁ → Θ (iS x₁))) k)
                       (Monotone.f (interpS (λ x₁ → subst (ren (Θ (iS x₁)) iS) (lem3' var v))) k)
  s-comp-r-lem-lem {Γ' = []} x Θ v k = <>
  s-comp-r-lem-lem {Γ' = x :: Γ'} x₁ Θ v k =
    s-comp-r-lem-lem x (throw-s Θ) v k ,
    Preorder-str.trans (snd [ x ]t)
      (Monotone.f (interpE (Θ (iS i0))) k)
      (Monotone.f (interpE (subst (Θ (iS i0)) (q v sr iS))) k)
      (Monotone.f (interpE (subst (ren (Θ (iS i0)) iS) (lem3' var v))) k)
        (s-id-l (Θ (iS i0)) k)
        (s-sr-r (q v) iS (Θ (iS i0)) k)

  s-comp-r-lem : ∀ {Γ Γ' τ1} (Θ : sctx Γ Γ') (v : Γ |- τ1) (k : fst [ Γ ]c)
               → Preorder-str.≤ (snd [ Γ' ]c)
                   (Monotone.f (interpS (λ x → Θ x)) k)
                   (Monotone.f (interpS (λ x → subst (ren (Θ x) iS) (lem3' (λ x₁ → var x₁) v))) k)
  s-comp-r-lem {Γ' = []} Θ v k = <>
  s-comp-r-lem {Γ' = x :: Γ'} Θ v k =
    s-comp-r-lem-lem x Θ v k ,
    (Preorder-str.trans (snd [ x ]t)
      (Monotone.f (interpE (Θ i0)) k)
      (Monotone.f (interpE (subst (Θ i0) (q v sr iS))) k)
      (Monotone.f (interpE (subst (ren (Θ i0) iS) (lem3' var v))) k)
        (s-id-l (Θ i0) k)
        (s-sr-r (q v) iS (Θ i0) k))

  s-comp2-l-lem-lem : ∀ {Γ Γ' τ1 τ2} (x : CTp) (Θ : sctx Γ (x :: Γ')) (v1 : Γ |- τ1) (v2 : Γ |- τ2) (k : fst [ Γ ]c)
                    → Preorder-str.≤ (snd [ Γ' ]c)
                        (Monotone.f (interpS (λ x₁ → subst (ren (ren (Θ (iS x₁)) iS) iS) (lem3' (lem3' ids v2) v1))) k)
                        (Monotone.f (interpS (λ x₁ → Θ (iS x₁))) k)
  s-comp2-l-lem-lem {Γ' = []} x Θ v1 v2 k = <>
  s-comp2-l-lem-lem {Γ' = x :: Γ'} x₁ Θ v1 v2 k =
    (s-comp2-l-lem-lem x (throw-s Θ) v1 v2 k) ,
    (Preorder-str.trans (snd [ x ]t)
      (Monotone.f (interpE (subst (ren (ren (Θ (iS i0)) iS) iS) (lem3' (lem3' ids v2) v1))) k)
      (Monotone.f (interpE (subst (ren (Θ (iS i0)) iS) (lem4 v1 v2 sr iS))) k)
      (Monotone.f (interpE (Θ (iS i0))) k)
        (s-sr-l (lem4 v1 v2) iS (ren (Θ (iS i0)) iS) k)
        (snd (s-comp-l-lem-lem x₁ Θ v2 k)))

  s-comp2-l-lem : ∀ {Γ Γ' τ1 τ2} (Θ : sctx Γ Γ') (v1 : Γ |- τ1) (v2 : Γ |- τ2) (k : fst [ Γ ]c)
                → Preorder-str.≤ (snd [ Γ' ]c)
                    (Monotone.f (interpS (λ x → subst (ren (ren (Θ x) iS) iS) (lem3' (lem3' ids v2) v1))) k)
                    (Monotone.f (interpS (λ x → Θ x)) k)
  s-comp2-l-lem {Γ' = []} Θ v1 v2 k = <>
  s-comp2-l-lem {Γ' = x :: Γ'} Θ v1 v2 k =
    s-comp2-l-lem-lem x Θ v1 v2 k ,
    (Preorder-str.trans (snd [ x ]t)
      (Monotone.f (interpE (subst (ren (ren (Θ i0) iS) iS) (lem3' (lem3' ids v2) v1))) k)
      (Monotone.f (interpE (subst (ren (Θ i0) iS) (lem4 v1 v2 sr iS))) k)
      (Monotone.f (interpE (Θ i0)) k)
        (s-sr-l (lem4 v1 v2) iS (ren (Θ i0) iS) k)
        (snd (s-comp-l-lem Θ v2 k)))

  s-comp2-r-lem-lem : ∀ {Γ Γ' τ1 τ2} (x : CTp) (Θ : sctx Γ (x :: Γ')) (v1 : Γ |- τ1) (v2 : Γ |- τ2) (k : fst [ Γ ]c)
                    → Preorder-str.≤ (snd [ Γ' ]c)
                        (Monotone.f (interpS (λ x₁ → Θ (iS x₁))) k)
                        (Monotone.f (interpS (λ x₁ → subst (ren (ren (Θ (iS x₁)) iS) iS) (lem3' (lem3' ids v2) v1))) k)
  s-comp2-r-lem-lem {Γ' = []} x Θ v1 v2 k = <>
  s-comp2-r-lem-lem {Γ' = x :: Γ'} x₁ Θ v1 v2 k =
    (s-comp2-r-lem-lem x (throw-s Θ) v1 v2 k) ,
    (Preorder-str.trans (snd [ x ]t)
      (Monotone.f (interpE (Θ (iS i0))) k)
      (Monotone.f (interpE (subst (ren (Θ (iS i0)) iS) (lem4 v1 v2 sr iS))) k)
      (Monotone.f (interpE (subst (ren (ren (Θ (iS i0)) iS) iS) (lem3' (lem3' ids v2) v1))) k)
        (snd (s-comp-r-lem-lem x₁ Θ v2 k)))
        (s-sr-r (lem4 v1 v2) iS (ren (Θ (iS i0)) iS) k)

  s-comp2-r-lem : ∀ {Γ Γ' τ1 τ2} (Θ : sctx Γ Γ') (v1 : Γ |- τ1) (v2 : Γ |- τ2) (k : fst [ Γ ]c)
                → Preorder-str.≤ (snd [ Γ' ]c)
                    (Monotone.f (interpS (λ x → Θ x)) k)
                    (Monotone.f (interpS (λ x → subst (ren (ren (Θ x) iS) iS) (lem3' (lem3' ids v2) v1))) k)
  s-comp2-r-lem {Γ' = []} Θ v1 v2 k = <>
  s-comp2-r-lem {Γ' = x :: Γ'} Θ v1 v2 k =
    s-comp2-r-lem-lem x Θ v1 v2 k ,
    (Preorder-str.trans (snd [ x ]t)
      (Monotone.f (interpE (Θ i0)) k)
      (Monotone.f (interpE (subst (ren (Θ i0) iS) (lem4 v1 v2 sr iS))) k)
      (Monotone.f (interpE (subst (ren (ren (Θ i0) iS) iS) (lem3' (lem3' ids v2) v1))) k)
        (snd (s-comp-r-lem Θ v2 k)))
        (s-sr-r (lem4 v1 v2) iS (ren (Θ i0) iS) k)

  s-comp3-l-lem-lem : ∀ {Γ Γ' τ1 τ2 τ3} (x : CTp) (Θ : sctx Γ (x :: Γ')) (v1 : Γ |- τ1) (v2 : Γ |- τ2) (v3 : Γ |- τ3) (k : fst [ Γ ]c)
                    → Preorder-str.≤ (snd [ Γ' ]c)
                        (Monotone.f (interpS (λ x₁ → subst (ren (ren (ren (Θ (iS x₁)) iS) iS) iS) (lem3' (lem3' (lem3' ids v3) v2) v1))) k)
                        (Monotone.f (interpS (λ x₁ → Θ (iS x₁))) k)
  s-comp3-l-lem-lem {Γ' = []} x Θ v1 v2 v3 k = <>
  s-comp3-l-lem-lem {Γ' = x :: Γ'} x₁ Θ v1 v2 v3 k =
    (s-comp3-l-lem-lem x (throw-s Θ) v1 v2 v3 k) ,
    (Preorder-str.trans (snd [ x ]t)
      (snd (Monotone.f (interpS (λ x₂ → subst (ren (ren (ren (Θ (iS x₂)) iS) iS) iS) (lem3' (lem3' (lem3' ids v3) v2) v1))) k))
      (Monotone.f (interpE (subst (ren (ren (Θ (iS i0)) iS) iS) (lem5 v1 v2 v3 sr iS))) k)
      (snd (Monotone.f (interpS (λ x₂ → Θ (iS x₂))) k))
        (s-sr-l (lem5 v1 v2 v3) iS (ren (ren (Θ (iS i0)) iS) iS) k)
        (snd (s-comp2-l-lem-lem x₁ Θ v2 v3 k)))

  s-comp3-l-lem : ∀ {Γ Γ' τ1 τ2 τ3} (Θ : sctx Γ Γ') (v1 : Γ |- τ1) (v2 : Γ |- τ2) (v3 : Γ |- τ3) (k : fst [ Γ ]c)
                → Preorder-str.≤ (snd [ Γ' ]c)
                    (Monotone.f (interpS (λ x → subst (ren (ren (ren (Θ x) (iS)) (iS)) (iS)) (lem3' (lem3' (lem3' ids v3) v2) v1))) k)
                    (Monotone.f (interpS (λ x → Θ x)) k)
  s-comp3-l-lem {Γ' = []} Θ v1 v2 v3 k = <>
  s-comp3-l-lem {Γ' = x :: Γ'} Θ v1 v2 v3 k =
    s-comp3-l-lem-lem x Θ v1 v2 v3 k ,
    (Preorder-str.trans (snd [ x ]t)
      (snd (Monotone.f (interpS (λ x₁ → subst (ren (ren (ren (Θ x₁) iS) iS) iS) (lem3' (lem3' (lem3' ids v3) v2) v1))) k))
      (Monotone.f (interpE (subst (ren (ren (Θ i0) iS) iS) (lem5 v1 v2 v3 sr iS))) k)
      (snd (Monotone.f (interpS Θ) k))
        (s-sr-l (lem5 v1 v2 v3) iS (ren (ren (Θ i0) iS) iS) k)
        (snd (s-comp2-l-lem Θ v2 v3 k)))

  s-comp3-r-lem-lem : ∀ {Γ Γ' τ1 τ2 τ3} (x : CTp) (Θ : sctx Γ (x :: Γ')) (v1 : Γ |- τ1) (v2 : Γ |- τ2) (v3 : Γ |- τ3) (k : fst [ Γ ]c)
                    → Preorder-str.≤ (snd [ Γ' ]c)
                        (Monotone.f (interpS (λ x₁ → Θ (iS x₁))) k)
                        (Monotone.f (interpS (λ x₁ → subst (ren (ren (ren (Θ (iS x₁)) iS) iS) iS) (lem3' (lem3' (lem3' ids v3) v2) v1))) k)
  s-comp3-r-lem-lem {Γ' = []} x Θ v1 v2 v3 k = <>
  s-comp3-r-lem-lem {Γ' = x :: Γ'} x₁ Θ v1 v2 v3 k =
    (s-comp3-r-lem-lem x (throw-s Θ) v1 v2 v3 k) ,
    (Preorder-str.trans (snd [ x ]t)
      (snd (Monotone.f (interpS (λ x₂ → Θ (iS x₂))) k))
      (Monotone.f (interpE (subst (ren (ren (Θ (iS i0)) iS) iS) (lem5 v1 v2 v3 sr iS))) k)
      (snd (Monotone.f (interpS (λ x₂ → subst (ren (ren (ren (Θ (iS x₂)) iS) iS) iS) (lem3' (lem3' (lem3' ids v3) v2) v1))) k))
        ((snd (s-comp2-r-lem-lem x₁ Θ v2 v3 k)))
        (s-sr-r (lem5 v1 v2 v3) iS (ren (ren (Θ (iS i0)) iS) iS) k))

  s-comp3-r-lem : ∀ {Γ Γ' τ1 τ2 τ3} (Θ : sctx Γ Γ') (v1 : Γ |- τ1) (v2 : Γ |- τ2) (v3 : Γ |- τ3) (k : fst [ Γ ]c)
                → Preorder-str.≤ (snd [ Γ' ]c)
                    (Monotone.f (interpS (λ x → Θ x)) k)
                    (Monotone.f (interpS (λ x → subst (ren (ren (ren (Θ x) (iS)) (iS)) (iS)) (lem3' (lem3' (lem3' ids v3) v2) v1))) k)
  s-comp3-r-lem {Γ' = []} Θ v1 v2 v3 k = <>
  s-comp3-r-lem {Γ' = x :: Γ'} Θ v1 v2 v3 k =
    s-comp3-r-lem-lem x Θ v1 v2 v3 k ,
    (Preorder-str.trans (snd [ x ]t)
      (snd (Monotone.f (interpS Θ) k))
      (Monotone.f (interpE (subst (ren (ren (Θ i0) iS) iS) (lem5 v1 v2 v3 sr iS))) k)
      (snd (Monotone.f (interpS (λ x₁ → subst (ren (ren (ren (Θ x₁) iS) iS) iS) (lem3' (lem3' (lem3' ids v3) v2) v1))) k))
        (snd (s-comp2-r-lem Θ v2 v3 k)))
        (s-sr-r (lem5 v1 v2 v3) iS (ren (ren (Θ i0) iS) iS) k)

  s-cong2-lem-lem : ∀ {Γ Γ'} (Θ Θ' : sctx Γ Γ') (x : (τ₁ : CTp) (x₁ : τ₁ ∈ Γ') → Θ x₁ ≤s Θ' x₁) (k : fst [ Γ ]c)
                  → Preorder-str.≤ (snd [ Γ' ]c) (Monotone.f (interpS Θ) k) (Monotone.f (interpS Θ') k)
  s-cong2-lem-lem {Γ' = []} Θ Θ' x k = <>
  s-cong2-lem-lem {Γ' = x :: Γ'} Θ Θ' x₁ k =
    s-cong2-lem-lem (throw-s Θ) (throw-s Θ') (λ τ₁ x₂ → x₁ τ₁ (iS x₂)) k ,
    sound (Θ i0) (Θ' i0) (x₁ x i0) k

  lam-s-lem : ∀ {Γ} (k : fst [ Γ ]c) → Preorder-str.≤ (snd [ Γ ]c) (Monotone.f (interpS {Γ} {Γ} ids) k) k
  lam-s-lem {[]} k = <>
  lam-s-lem {x :: Γ} (k1 , k2) =
    (Preorder-str.trans (snd [ Γ ]c)
      (Monotone.f (interpS {x :: Γ} {Γ} (throw-s ids)) (k1 , k2))
      (Monotone.f (interpS {Γ} {Γ} ids) k1)
      k1
        (subst-eq-l-lam {Γ} {Γ} ids k1 (Monotone.f (interpE {x :: Γ} {x} (ids i0)) (k1 , k2)))
        (lam-s-lem {Γ} k1)) ,
    (Preorder-str.refl (snd [ x ]t) k2)

{-
  sound {_} {τ} e .e refl-s k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {Γ} {τ} e e' (trans-s {.Γ} {.τ} {.e} {e''} {.e'} d d₁) k =
    Preorder-str.trans (snd [ τ ]t) (Monotone.f (interpE e) k) (Monotone.f (interpE e'') k) (Monotone.f (interpE e') k) (sound e e'' d k) (sound e'' e' d₁ k)
  sound {_} {τ} e .e (cong-refl Refl) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound .(plusC 0C e') e' +-unit-l k = Preorder-str.refl (snd [ rnat ]t) (Monotone.f (interpE e') k)
  sound e .(plusC 0C e) +-unit-l' k = Preorder-str.refl (snd [ rnat ]t) (Monotone.f (interpE e) k)
  sound {_} {.C} .(plusC e' 0C) e' +-unit-r k = +-unit (Monotone.f (interpE e') k)
  sound e .(plusC e 0C) +-unit-r' k = plus-lem' (Monotone.f (interpE e) k) (Monotone.f (interpE e) k) Z (nat-refl (Monotone.f (interpE e) k))
  sound {Γ} {.C} ._ ._ (+-assoc {.Γ} {e1} {e2} {e3}) k = plus-assoc (Monotone.f (interpE e1) k) (Monotone.f (interpE e2) k) (Monotone.f (interpE e3) k)
  sound {Γ} {.C} ._ ._ (+-assoc' {.Γ} {e1} {e2} {e3}) k = plus-assoc' (Monotone.f (interpE e1) k) (Monotone.f (interpE e2) k) (Monotone.f (interpE e3) k)
  sound {Γ} {.C} ._ ._ (refl-+ {.Γ} {e0} {e1}) k = +-comm (Monotone.f (interpE e0) k) (Monotone.f (interpE e1) k)
  sound {Γ} {C} ._ ._ (cong-+ {.Γ} {e0} {e1} {e0'} {e1'} d d₁) k = --also called plus-s. should really delete this rule so we don't have duplicates
    plus-lem (Monotone.f (interpE e0) k) (Monotone.f (interpE e1) k) (Monotone.f (interpE e0') k) (Monotone.f (interpE e1') k)
      (sound e0 e0' d k) (sound e1 e1' d₁ k)
  sound {Γ} {τ} ._ ._ (cong-lproj {.Γ} {.τ} {_} {e} {e'} d) k = fst (sound e e' d k)
  sound {Γ} {τ} ._ ._ (cong-rproj {.Γ} {_} {.τ} {e} {e'} d) k = snd (sound e e' d k)
  sound {Γ} {τ} ._ ._ (cong-app {.Γ} {τ'} {.τ} {e} {e'} {e1} d) k = sound e e' d k (Monotone.f (interpE e1) k)
  sound {Γ} {τ} ._ ._ (ren-cong {.Γ} {Γ'} {.τ} {e1} {e2} {ρ} d) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (ren e1 ρ)) k)
      (Monotone.f (interpE e1) (Monotone.f (interpR ρ) k))
      (Monotone.f (interpE (ren e2 ρ)) k)
        (ren-eq-l ρ e1 k)
        (Preorder-str.trans (snd [ τ ]t)
           (Monotone.f (interpE e1) (Monotone.f (interpR ρ) k))
           (Monotone.f (interpE e2) (Monotone.f (interpR ρ) k))
           (Monotone.f (interpE (ren e2 ρ)) k)
             (sound e1 e2 d (Monotone.f (interpR ρ) k))
             (ren-eq-r ρ e2 k))
  sound {Γ} {τ} ._ ._ (subst-cong {.Γ} {Γ'} {.τ} {e1} {e2} {Θ} d) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e1 Θ)) k)
      (Monotone.f (interpE e1) (Monotone.f (interpS Θ) k))
      (Monotone.f (interpE (subst e2 Θ)) k)
        (subst-eq-l Θ e1 k)
        (Preorder-str.trans (snd [ τ ]t)
           (Monotone.f (interpE e1) (Monotone.f (interpS Θ) k))
           (Monotone.f (interpE e2) (Monotone.f (interpS Θ) k))
           (Monotone.f (interpE (subst e2 Θ)) k)
             (sound e1 e2 d (Monotone.f (interpS Θ) k))
             (subst-eq-r Θ e2 k))
  sound {Γ} {τ} ._ ._ (subst-cong2 {.Γ} {Γ'} {.τ} {Θ} {Θ'} {e} x) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e Θ)) k)
      (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
      (Monotone.f (interpE (subst e Θ')) k) (subst-eq-l Θ e k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
          (Monotone.f (interpE e) (Monotone.f (interpS Θ') k))
          (Monotone.f (interpE (subst e Θ')) k)
            (Monotone.is-monotone (interpE e) (Monotone.f (interpS Θ) k)
            (Monotone.f (interpS Θ') k) (s-cong2-lem-lem Θ Θ' x k))
        (subst-eq-r Θ' e k))
  sound {Γ} {τ} ._ ._ (cong-rec {.Γ} {.τ} {e} {e'} {e0} {e1} d) k =
    ♭h-fix-args (interpE e0) (interpE e1) (k , Monotone.f (interpE e) k) (k , Monotone.f (interpE e') k) (sound e e' d k)
  sound {Γ} {τ} ._ ._ (cong-listrec {.Γ} {τ'} {.τ} {e} {e'} {e0} {e1} d) k =
    listrec-fix-args (interpE e0) (interpE e1) (k , (Monotone.f (interpE e) k)) (k , Monotone.f (interpE e') k) ((Preorder-str.refl (snd [ Γ ]c) k) , (sound e e' d k))
  sound {Γ} {τ} ._ ._ (lam-s {.Γ} {τ'} {.τ} {e} {e2}) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e (q e2))) k)
      (Monotone.f (interpE e) (Monotone.f (interpS (q e2)) k))
      (Monotone.f (interpE e) (k , Monotone.f (interpE e2) k))
        (subst-eq-l (q e2) e k)
        (Monotone.is-monotone (interpE e)
          (Monotone.f (interpS (q e2)) k)
          (k , Monotone.f (interpE e2) k)
            (lam-s-lem {Γ} k , (Preorder-str.refl (snd [ τ' ]t) (Monotone.f (interpE e2) k))))
  sound {Γ} {τ} e ._ (l-proj-s {.Γ}) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {Γ} {τ} e ._ (r-proj-s {.Γ}) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {_} {τ} e ._ rec-steps-z k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {Γ} {τ} ._ ._ (rec-steps-s {.Γ} {.τ} {e} {e0} {e1}) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e1 (lem3' (lem3' ids (rec e e0 e1)) e))) k)
      (Monotone.f (interpE e1) (Monotone.f (interpS (lem3' (lem3' ids (rec e e0 e1)) e)) k))
      (Monotone.f (interpE e1)
      ((k , natrec (Monotone.f (interpE e0) k) (λ n x₂ → Monotone.f (interpE e1) ((k , x₂) , n)) (Monotone.f (interpE e) k)) , Monotone.f (interpE e) k))
        (subst-eq-l (lem3' (lem3' ids (rec e e0 e1)) e) e1 k)
        (Monotone.is-monotone (interpE e1)
          (Monotone.f (interpS (lem3' (lem3' ids (rec e e0 e1)) e)) k)
          ((k , natrec (Monotone.f (interpE e0) k)
          (λ n x₂ → Monotone.f (interpE e1) ((k , x₂) , n)) (Monotone.f (interpE e) k)) , Monotone.f (interpE e) k)
            ((lam-s-lem {Γ} k ,
            (Preorder-str.refl (snd [ τ ]t) (natrec (Monotone.f (interpE e0) k) (λ n x₂ → Monotone.f (interpE e1) ((k , x₂) , n)) (Monotone.f (interpE e) k)))) ,
            (♭nat-refl (Monotone.f (interpE e) k))))
  sound {Γ} {τ} e ._ listrec-steps-nil k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {Γ} {τ} ._ ._ (listrec-steps-cons {.Γ} {τ'} {.τ} {h} {t} {e0} {e1}) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e1 (lem3' (lem3' (lem3' ids (listrec t e0 e1)) t) h))) k)
      (Monotone.f (interpE e1) (Monotone.f (interpS (lem3' (lem3' (lem3' ids (listrec t e0 e1)) t) h)) k))
      (Monotone.f (interpE e1)
       (((k ,
       lrec (Monotone.f (interpE t) k) (Monotone.f (interpE e0) k) (λ x₁ x₂ x₃ → Monotone.f (interpE e1) (((k , x₃) , x₂) , x₁))) ,
       Monotone.f (interpE t) k) ,
       Monotone.f (interpE h) k))
         (subst-eq-l (lem3' (lem3' (lem3' ids (listrec t e0 e1)) t) h) e1 k)
         (Monotone.is-monotone (interpE e1)
           (Monotone.f (interpS (lem3' (lem3' (lem3' ids (listrec t e0 e1)) t) h)) k)
           (((k , lrec (Monotone.f (interpE t) k) (Monotone.f (interpE e0) k) (λ x₁ x₂ x₃ → Monotone.f (interpE e1) (((k , x₃) , x₂) , x₁))) ,
           Monotone.f (interpE t) k) , Monotone.f (interpE h) k)
             (((lam-s-lem {Γ} k ,
             (Preorder-str.refl (snd [ τ ]t) (lrec (Monotone.f (interpE t) k) (Monotone.f (interpE e0) k) (λ x₁ x₂ x₃ → Monotone.f (interpE e1) (((k , x₃) , x₂) , x₁))))) ,
             (l-refl (snd [ τ' ]t) (Monotone.f (interpE t) k))) ,
             (Preorder-str.refl (snd [ τ' ]t) (Monotone.f (interpE h) k))))
  sound .(ren (ren e ρ2) ρ1) ._ (ren-comp-l ρ1 ρ2 e) k = s-rr-l e ρ1 ρ2 k
  sound ._ .(ren (ren e ρ2) ρ1) (ren-comp-r ρ1 ρ2 e) k = s-rr-r e ρ1 ρ2 k
  sound {Γ} {τ} e ._ (subst-id-l {.Γ} {.τ} .e) k = s-id-l e k
  sound ._ e' (subst-id-r .e') k = s-id-r e' k
  sound .(ren (subst e Θ) ρ) ._ (subst-rs-l ρ Θ e) k = s-rs-l ρ Θ e k
  sound ._ .(ren (subst e Θ) ρ) (subst-rs-r ρ Θ e) k = s-rs-r ρ Θ e k
  sound .(subst (ren e ρ) Θ) ._ (subst-sr-l Θ ρ e) k = s-sr-l Θ ρ e k
  sound ._ .(subst (ren e ρ) Θ) (subst-sr-r Θ ρ e) k = s-sr-r Θ ρ e k
  sound ._ .(subst (subst e Θ2) Θ1) (subst-ss-l Θ1 Θ2 e) k = s-ss-l Θ1 Θ2 e k
  sound .(subst (subst e Θ2) Θ1) ._ (subst-ss-r Θ1 Θ2 e) k = s-ss-r Θ1 Θ2 e k
  sound {τ = τ} ._ .(subst e (lem3' Θ v)) (subst-compose-l {_} {_} {τ1} {.τ} Θ v e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst (subst e (s-extend Θ)) (lem3' ids v))) k)
      (Monotone.f (interpE (subst e (lem3' ids v ss s-extend Θ))) k)
      (Monotone.f (interpE (subst e (lem3' Θ v))) k)
        (s-ss-r (lem3' ids v) (s-extend Θ) e k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e (lem3' ids v ss s-extend Θ))) k)
          (Monotone.f (interpE e) (Monotone.f (interpS (lem3' ids v ss s-extend Θ)) k))
          (Monotone.f (interpE (subst e (lem3' Θ v))) k)
            (subst-eq-l (lem3' ids v ss s-extend Θ) e k)
            (Preorder-str.trans (snd [ τ ]t)
              (Monotone.f (interpE e) (Monotone.f (interpS (lem3' ids v ss s-extend Θ)) k))
              (Monotone.f (interpE e) (Monotone.f (interpS (lem3' Θ v)) k))
              (Monotone.f (interpE (subst e (lem3' Θ v))) k)
                (Monotone.is-monotone (interpE e)
                  (Monotone.f (interpS (lem3' ids v ss s-extend Θ)) k)
                  (Monotone.f (interpS (lem3' Θ v)) k)
                    (s-comp-l-lem Θ v k , (Preorder-str.refl (snd [ τ1 ]t) (Monotone.f (interpE v) k))))
                (subst-eq-r (lem3' Θ v) e k)))
  sound {τ = τ} .(subst e (lem3' Θ v)) ._ (subst-compose-r {_} {_} {τ1} {.τ} Θ v e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e (lem3' Θ v))) k)
      (Monotone.f (interpE (subst e (lem3' ids v ss s-extend Θ))) k)
      (Monotone.f (interpE (subst (subst e (s-extend Θ)) (lem3' ids v))) k)
        (Preorder-str.trans (snd [ τ ]t)
           (Monotone.f (interpE (subst e (lem3' Θ v))) k)
           (Monotone.f (interpE e) (Monotone.f (interpS (lem3' ids v ss s-extend Θ)) k))
           (Monotone.f (interpE (subst e (lem3' ids v ss s-extend Θ))) k)
             (Preorder-str.trans (snd [ τ ]t)
               (Monotone.f (interpE (subst e (lem3' Θ v))) k)
               (Monotone.f (interpE e) (Monotone.f (interpS (lem3' Θ v)) k))
               (Monotone.f (interpE e) (Monotone.f (interpS (lem3' ids v ss s-extend Θ)) k))
                 (subst-eq-l (lem3' Θ v) e k)
                 (Monotone.is-monotone (interpE e)
                   (Monotone.f (interpS (lem3' Θ v)) k)
                   (Monotone.f (interpS (lem3' ids v ss s-extend Θ)) k)
                     (s-comp-r-lem Θ v k , (Preorder-str.refl (snd [ τ1 ]t) (Monotone.f (interpE v) k)))))
             (subst-eq-r (lem3' ids v ss s-extend Θ) e k))
        (s-ss-l (lem3' ids v) (s-extend Θ) e k)
  sound {τ = τ} ._ .(subst e1 (lem3' (lem3' Θ v2) v1)) (subst-compose2-l {_} {_} {.τ} {τ1} {τ2} Θ e1 v1 v2) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst (subst e1 (s-extend (s-extend Θ))) (lem4 v1 v2))) k)
      (Monotone.f (interpE (subst e1 (lem4 v1 v2 ss s-extend (s-extend Θ)))) k)
      (Monotone.f (interpE (subst e1 (lem3' (lem3' Θ v2) v1))) k)
        (s-ss-r (lem4 v1 v2) (s-extend (s-extend Θ)) e1 k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e1 (lem4 v1 v2 ss s-extend (s-extend Θ)))) k)
          (Monotone.f (interpE e1) (Monotone.f (interpS (lem4 v1 v2 ss s-extend (s-extend Θ))) k))
          (Monotone.f (interpE (subst e1 (lem3' (lem3' Θ v2) v1))) k)
            (subst-eq-l (lem4 v1 v2 ss s-extend (s-extend Θ)) e1 k)
            (Preorder-str.trans (snd [ τ ]t)
              (Monotone.f (interpE e1) (Monotone.f (interpS (lem4 v1 v2 ss s-extend (s-extend Θ))) k))
              (Monotone.f (interpE e1) (Monotone.f (interpS (lem4' Θ v1 v2)) k))
              (Monotone.f (interpE (subst e1 (lem3' (lem3' Θ v2) v1))) k)
                (Monotone.is-monotone (interpE e1)
                  (Monotone.f (interpS (lem4 v1 v2 ss s-extend (s-extend Θ))) k)
                  (Monotone.f (interpS (lem4' Θ v1 v2)) k)
                    (((s-comp2-l-lem Θ v1 v2 k) ,
                    (Preorder-str.refl (snd [ τ2 ]t) (Monotone.f (interpE v2) k))) ,
                    Preorder-str.refl (snd [ τ1 ]t) (Monotone.f (interpE v1) k)))
                (subst-eq-r (lem4' Θ v1 v2) e1 k)))
  sound {τ = τ} .(subst e1 (lem3' (lem3' Θ v2) v1)) ._ (subst-compose2-r {_} {_} {.τ} {τ1} {τ2} Θ e1 v1 v2) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e1 (lem3' (lem3' Θ v2) v1))) k)
      (Monotone.f (interpE (subst e1 (lem4 v1 v2 ss s-extend (s-extend Θ)))) k)
      (Monotone.f (interpE (subst (subst e1 (s-extend (s-extend Θ))) (lem4 v1 v2))) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e1 (lem3' (lem3' Θ v2) v1))) k)
          (Monotone.f (interpE e1) (Monotone.f (interpS (lem4 v1 v2 ss s-extend (s-extend Θ))) k))
          (Monotone.f (interpE (subst e1 (lem4 v1 v2 ss s-extend (s-extend Θ)))) k)
            (Preorder-str.trans (snd [ τ ]t)
              (Monotone.f (interpE (subst e1 (lem3' (lem3' Θ v2) v1))) k)
              (Monotone.f (interpE e1) (Monotone.f (interpS (lem4' Θ v1 v2)) k))
              (Monotone.f (interpE e1) (Monotone.f (interpS (lem4 v1 v2 ss s-extend (s-extend Θ))) k))
                (subst-eq-l (lem4' Θ v1 v2) e1 k)
                (Monotone.is-monotone (interpE e1)
                  (Monotone.f (interpS (lem4' Θ v1 v2)) k)
                  (Monotone.f (interpS (lem4 v1 v2 ss s-extend (s-extend Θ))) k)
                    ((s-comp2-r-lem Θ v1 v2 k ,
                    Preorder-str.refl (snd [ τ2 ]t) (Monotone.f (interpE v2) k)) ,
                    Preorder-str.refl (snd [ τ1 ]t) (Monotone.f (interpE v1) k))))
            (subst-eq-r (lem4 v1 v2 ss s-extend (s-extend Θ)) e1 k))
        (s-ss-l (lem4 v1 v2) (s-extend (s-extend Θ)) e1 k)
  sound {τ = τ} ._ .(subst e1 (lem3' (lem3' Θ (subst v2 Θ)) (subst v1 Θ))) (subst-compose3-l {_} {Γ'} {.τ} {τ1} {τ2} Θ e1 v1 v2) k =
   Preorder-str.trans (snd [ τ ]t)
     (Monotone.f (interpE (subst (subst e1 (lem4 v1 v2)) Θ)) k)
     (Monotone.f (interpE (subst e1 (Θ ss lem4 v1 v2))) k)
     (Monotone.f (interpE (subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ)))) k)
       (s-ss-r Θ (lem4 v1 v2) e1 k)
       (Preorder-str.trans (snd [ τ ]t)
         (Monotone.f (interpE (subst e1 (Θ ss lem4 v1 v2))) k)
         (Monotone.f (interpE e1) (Monotone.f (interpS (Θ ss lem4 v1 v2)) k))
         (Monotone.f (interpE (subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ)))) k)
           (subst-eq-l (Θ ss lem4 v1 v2) e1 k)
           (Preorder-str.trans (snd [ τ ]t)
             (Monotone.f (interpE e1) (Monotone.f (interpS (Θ ss lem4 v1 v2)) k))
             (Monotone.f (interpE e1) (Monotone.f (interpS (lem4' Θ (subst v1 Θ) (subst v2 Θ))) k))
             (Monotone.f (interpE (subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ)))) k)
               (Monotone.is-monotone (interpE e1)
                 (Monotone.f (interpS (Θ ss lem4 v1 v2)) k)
                 (Monotone.f (interpS (lem4' Θ (subst v1 Θ) (subst v2 Θ))) k)
                   ((Preorder-str.refl (snd [ Γ' ]c) (Monotone.f (interpS (λ x → Θ x)) k) ,
                   Preorder-str.refl (snd [ τ2 ]t) (Monotone.f (interpE (subst v2 Θ)) k)) ,
                   Preorder-str.refl (snd [ τ1 ]t) (Monotone.f (interpE (subst v1 Θ)) k)))
               (subst-eq-r (lem4' Θ (subst v1 Θ) (subst v2 Θ)) e1 k)))
  sound {τ = τ} .(subst e1 (lem3' (lem3' Θ (subst v2 Θ)) (subst v1 Θ))) ._ (subst-compose3-r {_} {Γ'} {.τ} {τ1} {τ2} Θ e1 v1 v2) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ)))) k)
      (Monotone.f (interpE (subst e1 (Θ ss lem4 v1 v2))) k)
      (Monotone.f (interpE (subst (subst e1 (lem4 v1 v2)) Θ)) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ)))) k)
          (Monotone.f (interpE e1) (Monotone.f (interpS (Θ ss lem4 v1 v2)) k))
          (Monotone.f (interpE (subst e1 (Θ ss lem4 v1 v2))) k)
            (Preorder-str.trans (snd [ τ ]t)
              (Monotone.f (interpE (subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ)))) k)
              (Monotone.f (interpE e1) (Monotone.f (interpS (lem4' Θ (subst v1 Θ) (subst v2 Θ))) k))
              (Monotone.f (interpE e1) (Monotone.f (interpS (Θ ss lem4 v1 v2)) k))
                (subst-eq-l (lem4' Θ (subst v1 Θ) (subst v2 Θ)) e1 k)
                (Monotone.is-monotone (interpE e1)
                  (Monotone.f (interpS (lem4' Θ (subst v1 Θ) (subst v2 Θ))) k)
                  (Monotone.f (interpS (Θ ss lem4 v1 v2)) k)
                    (((Preorder-str.refl (snd [ Γ' ]c) (Monotone.f (interpS (λ x → Θ x)) k)) ,
                    (Preorder-str.refl (snd [ τ2 ]t) (Monotone.f (interpE (subst v2 Θ)) k))) ,
                    (Preorder-str.refl (snd [ τ1 ]t) (Monotone.f (interpE (subst v1 Θ)) k)))))
            (subst-eq-r (Θ ss lem4 v1 v2) e1 k))
        (s-ss-l Θ (lem4 v1 v2) e1 k)
  sound ._ .(subst e2 (lem3' (lem3' Θ r) v')) (subst-compose4-l Θ v' r e2) k = sound _ (subst e2 (lem3' (lem3' Θ r) v')) (subst-compose2-l Θ e2 v' r) k
  sound .(subst e2 (lem3' (lem3' Θ r) v')) ._ (subst-compose4-r Θ v' r e2) k = sound (subst e2 (lem3' (lem3' Θ r) v')) _ (subst-compose2-r Θ e2 v' r) k
  sound {τ = τ} ._ .(subst e (lem3' (lem3' (lem3' Θ v3) v2) v1)) (subst-compose5-l {_} {_} {.τ} {τ1} {τ2} {τ3} Θ e v1 v2 v3) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst (subst e (s-extend (s-extend (s-extend Θ)))) (lem5 v1 v2 v3))) k)
      (Monotone.f (interpE (subst e (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ))))) k)
      (Monotone.f (interpE (subst e (lem5' Θ v1 v2 v3))) k)
        (s-ss-r (lem5 v1 v2 v3) (s-extend (s-extend (s-extend Θ))) e k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ))))) k)
          (Monotone.f (interpE e) (Monotone.f (interpS (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ)))) k))
          (Monotone.f (interpE (subst e (lem5' Θ v1 v2 v3))) k)
            (subst-eq-l (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ))) e k)
            (Preorder-str.trans (snd [ τ ]t)
              (Monotone.f (interpE e) (Monotone.f (interpS (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ)))) k))
              (Monotone.f (interpE e) (Monotone.f (interpS (lem5' Θ v1 v2 v3)) k))
              (Monotone.f (interpE (subst e (lem5' Θ v1 v2 v3))) k)
                (Monotone.is-monotone (interpE e)
                  (Monotone.f (interpS (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ)))) k)
                  (Monotone.f (interpS (lem5' Θ v1 v2 v3)) k)
                    (((s-comp3-l-lem Θ v1 v2 v3 k ,
                    Preorder-str.refl (snd [ τ3 ]t) (Monotone.f (interpE v3) k)) ,
                    Preorder-str.refl (snd [ τ2 ]t) (Monotone.f (interpE v2) k)) ,
                    Preorder-str.refl (snd [ τ1 ]t) (Monotone.f (interpE v1) k)))
                (subst-eq-r (lem5' Θ v1 v2 v3) e k)))
  sound {τ = τ} .(subst e (lem3' (lem3' (lem3' Θ v3) v2) v1)) ._ (subst-compose5-r {_} {_} {.τ} {τ1} {τ2} {τ3} Θ e v1 v2 v3) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e (lem5' Θ v1 v2 v3))) k)
      (Monotone.f (interpE (subst e (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ))))) k)
      (Monotone.f (interpE (subst (subst e (s-extend (s-extend (s-extend Θ)))) (lem5 v1 v2 v3))) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e (lem5' Θ v1 v2 v3))) k)
          (Monotone.f (interpE e) (Monotone.f (interpS (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ)))) k))
          (Monotone.f (interpE (subst e (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ))))) k)
            (Preorder-str.trans (snd [ τ ]t)
              (Monotone.f (interpE (subst e (lem5' Θ v1 v2 v3))) k)
              (Monotone.f (interpE e) (Monotone.f (interpS (lem5' Θ v1 v2 v3)) k))
              (Monotone.f (interpE e) (Monotone.f (interpS (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ)))) k))
                (subst-eq-l (lem5' Θ v1 v2 v3) e k)
                (Monotone.is-monotone (interpE e)
                  (Monotone.f (interpS (lem5' Θ v1 v2 v3)) k)
                  (Monotone.f (interpS (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ)))) k)
                    ((((s-comp3-r-lem Θ v1 v2 v3 k) ,
                    (Preorder-str.refl (snd [ τ3 ]t) (Monotone.f (interpE v3) k))) ,
                    (Preorder-str.refl (snd [ τ2 ]t) (Monotone.f (interpE v2) k))) ,
                    (Preorder-str.refl (snd [ τ1 ]t) (Monotone.f (interpE v1) k)))))
            (subst-eq-r (lem5 v1 v2 v3 ss s-extend (s-extend (s-extend Θ))) e k))
        (s-ss-l (lem5 v1 v2 v3) (s-extend (s-extend (s-extend Θ))) e k)
-}

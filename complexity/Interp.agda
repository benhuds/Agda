{- NEW INTERP FILE WITHOUT RREC -}

open import Preliminaries
open import Preorder
open import Pilot2

module Interp where

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
--  interpE rz = z'
--  interpE (rsuc e) = suc' (interpE e)
--  interpE (rrec e e₁ e₂ P) = comp (pair' id (interpE e)) (rec' (interpE e₁) (unlam' (unlam' (interpE e₂))) (λ x → sound e₁ (app (app e₂ rz) e₁) P x))
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
      (natrec (Monotone.f (interpE (ren e₁ ρ)) k)
        (λ n x₂ → Monotone.f (interpE (ren e₂ (r-extend (r-extend ρ)))) ((k , x₂) , n))
        (Monotone.f (interpE (ren e ρ)) k))
      (natrec (Monotone.f (interpE (ren e₁ ρ)) k)
        (λ n x₂ → Monotone.f (interpE (ren e₂ (r-extend (r-extend ρ)))) ((k , x₂) , n))
         (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
      (natrec (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))
        (λ n x₂ → Monotone.f (interpE e₂) ((Monotone.f (interpR ρ) k , x₂) , n))
        (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
      (♭h-fix-args (interpE (ren e₁ ρ)) (interpE (ren e₂ (r-extend (r-extend ρ))))
        (k , (Monotone.f (interpE (ren e ρ)) k))
        (k , (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
          (ren-eq-l ρ e k))
      (♭h-cong
        (interpE (ren e₁ ρ))
        (monotone (λ v → Monotone.f (interpE e₁) (Monotone.f (interpR ρ) v))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₁)
              (Monotone.f (interpR ρ) x)
              (Monotone.f (interpR ρ) y)
                (Monotone.is-monotone (interpR ρ) x y x₁)))
        (interpE (ren e₂ (r-extend (r-extend ρ))))
        (monotone (λ v → Monotone.f (interpE e₂) ((Monotone.f (interpR ρ) (fst (fst v)) , snd (fst v)) , snd v))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₂)
              ((Monotone.f (interpR ρ) (fst (fst x)) , snd (fst x)) , snd x)
              ((Monotone.f (interpR ρ) (fst (fst y)) , snd (fst y)) , snd y)
                (((Monotone.is-monotone (interpR ρ) (fst (fst x)) (fst (fst y)) (fst (fst x₁))) ,
                (snd (fst x₁))) ,
                (snd x₁))))
        (k , (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
          (λ x → ren-eq-l ρ e₁ x)
          (λ x →
            Preorder-str.trans (snd [ τ ]t)
              (Monotone.f (interpE (ren e₂ (r-extend (r-extend ρ)))) x)
              (Monotone.f (interpE e₂) (Monotone.f (interpR {nat :: τ :: Γ} {_ :: _ :: Γ'} (r-extend (r-extend ρ))) x))
              (Monotone.f (interpE e₂) ((Monotone.f (interpR ρ) (fst (fst x)) , snd (fst x)) , snd x))
                (ren-eq-l (r-extend (r-extend ρ)) e₂ x)
                (Monotone.is-monotone (interpE e₂)
                  (Monotone.f (interpR {nat :: τ :: Γ} {_ :: _ :: Γ'} (r-extend (r-extend ρ))) x)
                  ((Monotone.f (interpR ρ) (fst (fst x)) , snd (fst x)) , snd x)
                    ((Preorder-str.trans (snd [ Γ' ]c)
                       (Monotone.f (interpR (λ x₁ → iS (iS (ρ x₁)))) x)
                       (Monotone.f (interpR {τ :: Γ} {Γ'} (throw-r (r-extend ρ))) (fst (fst x) , snd (fst x)))
                       (Monotone.f (interpR ρ) (fst (fst x)))
                         (ren-eq-l-lam {τ :: Γ} {Γ'} (throw-r (r-extend ρ)) (fst x) (snd x))
                         (ren-eq-l-lam ρ (fst (fst x)) (snd (fst x))) ,
                    (Preorder-str.refl (snd [ τ ]t) (snd (fst x)))) ,
                    (♭nat-refl (snd x))))))
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
--  ren-eq-l ρ rz k = <>
--  ren-eq-l ρ (rsuc e) k = ren-eq-l ρ e k
{-  ren-eq-l {Γ} {Γ'} {τ} ρ (rrec e e₁ e₂ P) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (comp (pair' id (interpE (ren e ρ)))
        (rec' (interpE (ren e₁ ρ)) (unlam' (unlam' (interpE (ren e₂ ρ))))
        (sound (ren e₁ ρ) (app (app (ren e₂ ρ) rz) (ren e₁ ρ)) (ren-cong P)))) k)
      (Monotone.f (rec' (interpE (ren e₁ ρ)) (unlam' (unlam' (interpE (ren e₂ ρ))))
        (λ x₁ → sound (ren e₁ ρ) (app (app (ren e₂ ρ) rz) (ren e₁ ρ)) (ren-cong P) x₁))
        (k , Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
      (Monotone.f (comp (pair' id (interpE e))
        (rec' (interpE e₁) (unlam' (unlam' (interpE e₂)))
        (sound e₁ (app (app e₂ rz) e₁) P))) (Monotone.f (interpR ρ) k))
      (h-lem2 (interpE (ren e₁ ρ)) (unlam' (unlam' (interpE (ren e₂ ρ))))
        (k , Monotone.f (interpE (ren e ρ)) k)
        (k , Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
        (λ x → sound (ren e₁ ρ) (app (app (ren e₂ ρ) rz) (ren e₁ ρ)) (ren-cong P) x)
          (ren-eq-l ρ e k))
      (h-cong2 (interpE (ren e₁ ρ))
        (monotone
          (λ z₁ → Monotone.f (interpE e₁) (Monotone.f (interpR ρ) z₁))
          (λ x y x₁ →
             Monotone.is-monotone (interpE e₁)
               (Monotone.f (interpR ρ) x)
               (Monotone.f (interpR ρ) y)
                 (Monotone.is-monotone (interpR ρ) x y x₁)))
        (unlam' (unlam' (interpE (ren e₂ ρ))))
        (monotone
          (λ v → Monotone.f (Monotone.f (Monotone.f (interpE e₂) (Monotone.f (interpR ρ) (fst (fst v)))) (snd (fst v))) (snd v))
          (λ x y x₁ →
            Monotone.is-monotone (unlam' (unlam' (interpE e₂)))
              ((Monotone.f (interpR ρ) (fst (fst x)) , snd (fst x)) , snd x)
              ((Monotone.f (interpR ρ) (fst (fst y)) , snd (fst y)) , snd y)
                ((Monotone.is-monotone (interpR ρ) (fst (fst x)) (fst (fst y)) (fst (fst x₁)) , snd (fst x₁)) , snd x₁)))
         (λ x → ren-eq-l ρ e₁ x)
         (λ x → ren-eq-l ρ e₂ (fst (fst x)) (snd (fst x)) (snd x))
         (λ x₁ → sound (ren e₁ ρ) (app (app (ren e₂ ρ) rz) (ren e₁ ρ)) (ren-cong P) x₁)
         (λ x₁ → sound e₁ (app (app e₂ rz) e₁) P (Monotone.f (interpR ρ) x₁))
         (k , Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))-}
  ren-eq-l ρ (prod e e₁) k = (ren-eq-l ρ e k) , (ren-eq-l ρ e₁ k)
  ren-eq-l ρ (l-proj e) k = fst (ren-eq-l ρ e k)
  ren-eq-l ρ (r-proj e) k = snd (ren-eq-l ρ e k)
  ren-eq-l ρ nil k = <>
  ren-eq-l ρ (e ::c e₁) k = (ren-eq-l ρ e k) , (ren-eq-l ρ e₁ k)
  ren-eq-l {Γ} {Γ'} {τ = τ} ρ (listrec {.Γ'} {τ'} e e₁ e₂) k =
    Preorder-str.trans (snd [ τ ]t)
      (lrec (Monotone.f (interpE (ren e ρ)) k)
        (Monotone.f (interpE (ren e₁ ρ)) k)
        (λ x₁ x₂ x₃ → Monotone.f (interpE (ren e₂ (r-extend (r-extend (r-extend ρ))))) (((k , x₃) , x₂) , x₁)))
      (lrec (Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
        (Monotone.f (interpE (ren e₁ ρ)) k)
        (λ x₁ x₂ x₃ → Monotone.f (interpE (ren e₂ (r-extend (r-extend (r-extend ρ))))) (((k , x₃) , x₂) , x₁)))
      (lrec (Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
        (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))
        (λ x₁ x₂ x₃ → Monotone.f (interpE e₂) (((Monotone.f (interpR ρ) k , x₃) , x₂) , x₁)))
      (listrec-fix-args (interpE (ren e₁ ρ)) (interpE (ren e₂ (r-extend (r-extend (r-extend ρ)))))
        (k , (Monotone.f (interpE (ren e ρ)) k))
        (k , (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
        ((Preorder-str.refl (snd [ Γ ]c) k) , (ren-eq-l ρ e k)))
      (lrec-cong
        (interpE (ren e₁ ρ))
        (monotone (λ k₁ → Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k₁))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₁)
              (Monotone.f (interpR ρ) x) (Monotone.f (interpR ρ) y)
              (Monotone.is-monotone (interpR ρ) x y x₁)))
        (interpE (ren e₂ (r-extend (r-extend (r-extend ρ)))))
        (monotone (λ x → Monotone.f (interpE e₂) ((((Monotone.f (interpR ρ) (fst (fst (fst x)))) , (snd (fst (fst x)))) , (snd (fst x))) , (snd x)))
          (λ x y x₁ → Monotone.is-monotone (interpE e₂)
            (((Monotone.f (interpR ρ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x)
            (((Monotone.f (interpR ρ) (fst (fst (fst y))) , snd (fst (fst y))) , snd (fst y)) , snd y)
              ((((Monotone.is-monotone (interpR ρ) (fst (fst (fst x))) (fst (fst (fst y))) (fst (fst (fst x₁)))) ,
              (snd (fst (fst x₁)))) ,
              (snd (fst x₁))) ,
              (snd x₁))))
        (k , (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
          (λ x → ren-eq-l ρ e₁ x)
          (λ x →
            Preorder-str.trans (snd [ τ ]t)
              (Monotone.f (interpE (ren e₂ (r-extend (r-extend (r-extend ρ))))) x)
              (Monotone.f (interpE e₂) (Monotone.f (interpR {τ' :: list τ' :: τ :: Γ} {_ :: _ :: _ :: Γ'} (r-extend (r-extend (r-extend ρ)))) x))
              (Monotone.f (interpE e₂) (((Monotone.f (interpR ρ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x))
              (ren-eq-l (r-extend (r-extend (r-extend ρ))) e₂ x)
              (Monotone.is-monotone (interpE e₂)
                (Monotone.f (interpR {τ' :: list τ' :: τ :: Γ} {_ :: _ :: _ :: Γ'} (r-extend (r-extend (r-extend ρ)))) x)
                (((Monotone.f (interpR ρ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x)
                  (((Preorder-str.trans (snd [ Γ' ]c)
                    (Monotone.f (interpR (λ x₁ → iS (iS (iS (ρ x₁))))) x)
                    (Monotone.f (interpR {τ :: Γ} {Γ'} (throw-r (r-extend ρ))) (fst (fst (fst x)) , snd (fst (fst x))))
                    (Monotone.f (interpR ρ) (fst (fst (fst x))))
                      (Preorder-str.trans (snd [ Γ' ]c)
                        (Monotone.f (interpR (λ x₁ → iS (iS (iS (ρ x₁))))) x)
                        (Monotone.f (interpR (λ x₁ → iS (iS (ρ x₁)))) (fst x))
                        (Monotone.f (interpR {τ :: Γ} {Γ'} (throw-r (r-extend ρ))) (fst (fst (fst x)) , snd (fst (fst x))))
                          (ren-eq-l-lam (λ x₁ → iS (iS (ρ x₁))) (fst x) (snd x))
                          (ren-eq-l-lam (λ x₁ → iS (ρ x₁)) (fst (fst x)) (snd (fst x))))
                      (ren-eq-l-lam ρ (fst (fst (fst x))) (snd (fst (fst x)))) ,
                  Preorder-str.refl (snd [ τ ]t) (snd (fst (fst x)))) ,
                  l-refl (snd [ τ' ]t) (snd (fst x))) ,
                  Preorder-str.refl (snd [ τ' ]t) (snd x)))))
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
  ren-eq-r {Γ} {Γ'} {τ} ρ (rec e e₁ e₂) k =
    Preorder-str.trans (snd [ τ ]t)
      (natrec (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))
        (λ n x₂ → Monotone.f (interpE e₂) ((Monotone.f (interpR ρ) k , x₂) , n))
        (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
      (natrec (Monotone.f (interpE (ren e₁ ρ)) k)
        (λ n x₂ → Monotone.f (interpE (ren e₂ (r-extend (r-extend ρ)))) ((k , x₂) , n))
        (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
      (natrec (Monotone.f (interpE (ren e₁ ρ)) k)
        (λ n x₂ → Monotone.f (interpE (ren e₂ (r-extend (r-extend ρ)))) ((k , x₂) , n))
        (Monotone.f (interpE (ren e ρ)) k))
      (♭h-cong
        (monotone (λ v → Monotone.f (interpE e₁) (Monotone.f (interpR ρ) v))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₁) (Monotone.f (interpR ρ) x)
             (Monotone.f (interpR ρ) y)
             (Monotone.is-monotone (interpR ρ) x y x₁)))
        (interpE (ren e₁ ρ))
        (monotone (λ v → Monotone.f (interpE e₂) ((Monotone.f (interpR ρ) (fst (fst v)) , snd (fst v)) , snd v))
        (λ x y x₁ →
          Monotone.is-monotone (interpE e₂)
            ((Monotone.f (interpR ρ) (fst (fst x)) , snd (fst x)) , snd x)
            ((Monotone.f (interpR ρ) (fst (fst y)) , snd (fst y)) , snd y)
              ((Monotone.is-monotone (interpR ρ) (fst (fst x)) (fst (fst y)) (fst (fst x₁)) ,
              snd (fst x₁)) ,
              snd x₁)))
        (interpE (ren e₂ (r-extend (r-extend ρ))))
        (k , Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
          (λ x → ren-eq-r ρ e₁ x)
          (λ x →
            Preorder-str.trans (snd [ τ ]t)
              (Monotone.f (interpE e₂) ((Monotone.f (interpR ρ) (fst (fst x)) , snd (fst x)) , snd x))
              (Monotone.f (interpE e₂) (Monotone.f (interpR {nat :: τ :: Γ} {_ :: _ :: Γ'} (r-extend (r-extend ρ))) x))
              (Monotone.f (interpE (ren e₂ (r-extend (r-extend ρ)))) x)
                (Monotone.is-monotone (interpE e₂)
                  ((Monotone.f (interpR ρ) (fst (fst x)) , snd (fst x)) , snd x)
                  (Monotone.f (interpR {nat :: τ :: Γ} {_ :: _ :: Γ'} (r-extend (r-extend ρ))) x)
                    (((Preorder-str.trans (snd [ Γ' ]c)
                      (Monotone.f (interpR ρ) (fst (fst x)))
                      (Monotone.f (interpR {τ :: Γ} {Γ'} (throw-r (r-extend ρ))) (fst (fst x) , snd (fst x)))
                      (Monotone.f (interpR (λ x₁ → iS (iS (ρ x₁)))) x)
                        (ren-eq-r-lam ρ (fst (fst x)) (snd (fst x)))
                        (ren-eq-r-lam {τ :: Γ} {Γ'} (throw-r (r-extend ρ)) (fst x) (snd x))) ,
                    (Preorder-str.refl (snd [ τ ]t) (snd (fst x)))) ,
                    (♭nat-refl (snd x))))
                (ren-eq-r (r-extend (r-extend ρ)) e₂ x)))
      (♭h-fix-args (interpE (ren e₁ ρ))
         (interpE (ren e₂ (r-extend (r-extend ρ))))
         (k , Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
         (k , Monotone.f (interpE (ren e ρ)) k) (ren-eq-r ρ e k))
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
{-  ren-eq-r ρ rz k = <>
  ren-eq-r ρ (rsuc e) k = ren-eq-r ρ e k
  ren-eq-r {Γ} {Γ'} {τ} ρ (rrec e e₁ e₂ P) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (comp (pair' id (interpE e))
        (rec' (interpE e₁) (unlam' (unlam' (interpE e₂)))
        (sound e₁ (app (app e₂ rz) e₁) P))) (Monotone.f (interpR ρ) k))
      (Monotone.f (rec' (interpE (ren e₁ ρ)) (unlam' (unlam' (interpE (ren e₂ ρ))))
        (λ x₁ → sound (ren e₁ ρ) (app (app (ren e₂ ρ) rz) (ren e₁ ρ)) (ren-cong P) x₁))
        (k , Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
      (Monotone.f (comp (pair' id (interpE (ren e ρ)))
        (rec' (interpE (ren e₁ ρ)) (unlam' (unlam' (interpE (ren e₂ ρ))))
        (sound (ren e₁ ρ) (app (app (ren e₂ ρ) rz) (ren e₁ ρ)) (ren-cong P)))) k)
      (h-cong2
        (monotone (λ z₁ → Monotone.f (interpE e₁) (Monotone.f (interpR ρ) z₁))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₁)
              (Monotone.f (interpR ρ) x)
              (Monotone.f (interpR ρ) y)
                (Monotone.is-monotone (interpR ρ) x y x₁)))
        (interpE (ren e₁ ρ))
        (monotone (λ v → Monotone.f (Monotone.f (Monotone.f (interpE e₂) (Monotone.f (interpR ρ) (fst (fst v)))) (snd (fst v))) (snd v))
          (λ x y x₁ →
            Monotone.is-monotone (unlam' (unlam' (interpE e₂)))
              ((Monotone.f (interpR ρ) (fst (fst x)) , snd (fst x)) , snd x)
              ((Monotone.f (interpR ρ) (fst (fst y)) , snd (fst y)) , snd y)
                ((Monotone.is-monotone (interpR ρ) (fst (fst x)) (fst (fst y)) (fst (fst x₁)) , snd (fst x₁)) , snd x₁)))
        (unlam' (unlam' (interpE (ren e₂ ρ))))
        (λ x → ren-eq-r ρ e₁ x)
        (λ x → ren-eq-r ρ e₂ (fst (fst x)) (snd (fst x)) (snd x))
        (λ x₁ → sound e₁ (app (app e₂ rz) e₁) P (Monotone.f (interpR ρ) x₁))
        (λ x₁ → sound (ren e₁ ρ) (app (app (ren e₂ ρ) rz) (ren e₁ ρ)) (ren-cong P) x₁)
        (k , (Monotone.f (interpE e) (Monotone.f (interpR ρ) k))))
      (h-lem2 (interpE (ren e₁ ρ)) (unlam' (unlam' (interpE (ren e₂ ρ))))
        (k , Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
        (k , Monotone.f (interpE (ren e ρ)) k)
        (λ x → sound (ren e₁ ρ) (app (app (ren e₂ ρ) rz) (ren e₁ ρ)) (ren-cong P) x)
          (ren-eq-r ρ e k))-}
  ren-eq-r ρ (prod e e₁) k = (ren-eq-r ρ e k) , (ren-eq-r ρ e₁ k)
  ren-eq-r ρ (l-proj e) k = fst (ren-eq-r ρ e k)
  ren-eq-r ρ (r-proj e) k = snd (ren-eq-r ρ e k)
  ren-eq-r ρ nil k = <>
  ren-eq-r ρ (e ::c e₁) k = (ren-eq-r ρ e k) , (ren-eq-r ρ e₁ k)
  ren-eq-r {Γ} {Γ'} {τ} ρ (listrec {.Γ'} {τ'} e e₁ e₂) k =
    Preorder-str.trans (snd [ τ ]t)
      (lrec (Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
        (Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k))
        (λ x₁ x₂ x₃ → Monotone.f (interpE e₂) (((Monotone.f (interpR ρ) k , x₃) , x₂) , x₁)))
      (lrec (Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
        (Monotone.f (interpE (ren e₁ ρ)) k)
        (λ x₁ x₂ x₃ → Monotone.f (interpE (ren e₂ (r-extend (r-extend (r-extend ρ))))) (((k , x₃) , x₂) , x₁)))
      (lrec (Monotone.f (interpE (ren e ρ)) k)
        (Monotone.f (interpE (ren e₁ ρ)) k)
        (λ x₁ x₂ x₃ → Monotone.f (interpE (ren e₂ (r-extend (r-extend (r-extend ρ))))) (((k , x₃) , x₂) , x₁)))
      (lrec-cong
        (monotone (λ k₁ → Monotone.f (interpE e₁) (Monotone.f (interpR ρ) k₁))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₁)
              (Monotone.f (interpR ρ) x)
              (Monotone.f (interpR ρ) y)
              (Monotone.is-monotone (interpR ρ) x y x₁)))
        (interpE (ren e₁ ρ))
        (monotone (λ x → Monotone.f (interpE e₂) (((Monotone.f (interpR ρ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₂)
              (((Monotone.f (interpR ρ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x)
              (((Monotone.f (interpR ρ) (fst (fst (fst y))) , snd (fst (fst y))) , snd (fst y)) , snd y)
              (((Monotone.is-monotone (interpR ρ)
                (fst (fst (fst x))) (fst (fst (fst y))) (fst (fst (fst x₁))) ,
                snd (fst (fst x₁))) ,
                snd (fst x₁)) ,
                snd x₁)))
        (interpE (ren e₂ (r-extend (r-extend (r-extend ρ)))))
        (k , (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)))
          (λ x → ren-eq-r ρ e₁ x)
          (λ x →
            Preorder-str.trans (snd [ τ ]t)
              (Monotone.f (interpE e₂) (((Monotone.f (interpR ρ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x))
              (Monotone.f (interpE e₂) (Monotone.f (interpR {τ' :: list τ' :: τ :: Γ} {_ :: _ :: _ :: Γ'} (r-extend (r-extend (r-extend ρ)))) x))
              (Monotone.f (interpE (ren e₂ (r-extend (r-extend (r-extend ρ))))) x)
                (Monotone.is-monotone (interpE e₂)
                  (((Monotone.f (interpR ρ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x)
                  (Monotone.f (interpR {τ' :: list τ' :: τ :: Γ} {_ :: _ :: _ :: Γ'} (r-extend (r-extend (r-extend ρ)))) x)
                    ((((Preorder-str.trans (snd [ Γ' ]c)
                      (Monotone.f (interpR ρ) (fst (fst (fst x))))
                      (Monotone.f (interpR {τ :: Γ} {Γ'} (throw-r (r-extend ρ))) (fst (fst (fst x)) , snd (fst (fst x))))
                      (Monotone.f (interpR (λ x₁ → iS (iS (iS (ρ x₁))))) x)
                        (ren-eq-r-lam ρ (fst (fst (fst x))) (snd (fst (fst x))))
                        (Preorder-str.trans (snd [ Γ' ]c)
                          (Monotone.f (interpR {τ :: Γ} {Γ'} (throw-r (r-extend ρ))) (fst (fst (fst x)) , snd (fst (fst x))))
                          (Monotone.f (interpR (λ x₁ → iS (iS (ρ x₁)))) (fst x))
                          (Monotone.f (interpR (λ x₁ → iS (iS (iS (ρ x₁))))) x)
                            (ren-eq-r-lam (λ x₁ → iS (ρ x₁)) (fst (fst x)) (snd (fst x)))
                            (ren-eq-r-lam (λ x₁ → iS (iS (ρ x₁))) (fst x) (snd x)))) ,
                    (Preorder-str.refl (snd [ τ ]t) (snd (fst (fst x))))) ,
                    (l-refl (snd [ τ' ]t) (snd (fst x)))) ,
                    (Preorder-str.refl (snd [ τ' ]t) (snd x))))
                (ren-eq-r (r-extend (r-extend (r-extend ρ))) e₂ x)))
      (listrec-fix-args (interpE (ren e₁ ρ)) (interpE (ren e₂ (r-extend (r-extend (r-extend ρ)))))
        (k , Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
        (k , Monotone.f (interpE (ren e ρ)) k)
        (Preorder-str.refl (snd [ Γ ]c) k , ren-eq-r ρ e k))
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
  subst-eq-l {Γ} {Γ'} {τ} Θ (rec e e₁ e₂) k =
    Preorder-str.trans (snd [ τ ]t)
      (natrec (Monotone.f (interpE (subst e₁ Θ)) k)
        (λ n x₂ → Monotone.f (interpE (subst e₂ (s-extend (s-extend Θ)))) ((k , x₂) , n))
        (Monotone.f (interpE (subst e Θ)) k))
      (natrec (Monotone.f (interpE (subst e₁ Θ)) k)
        (λ n x₂ → Monotone.f (interpE (subst e₂ (s-extend (s-extend Θ)))) ((k , x₂) , n))
        (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)))
      (natrec (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k))
        (λ n x₂ → Monotone.f (interpE e₂) ((Monotone.f (interpS Θ) k , x₂) , n))
        (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)))
      (♭h-fix-args (interpE (subst e₁ Θ)) (interpE (subst e₂ (s-extend (s-extend Θ))))
        (k , Monotone.f (interpE (subst e Θ)) k)
        (k , Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
          (subst-eq-l Θ e k))
      (♭h-cong
        (interpE (subst e₁ Θ))
        (monotone (λ v → Monotone.f (interpE e₁) (Monotone.f (interpS Θ) v))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₁) (Monotone.f (interpS Θ) x) (Monotone.f (interpS Θ) y) (Monotone.is-monotone (interpS Θ) x y x₁)))
        (interpE (subst e₂ (s-extend (s-extend Θ))))
        (monotone (λ v → Monotone.f (interpE e₂) ((Monotone.f (interpS Θ) (fst (fst v)) , snd (fst v)) , snd v))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₂)
             ((Monotone.f (interpS Θ) (fst (fst x)) , snd (fst x)) , snd x)
             ((Monotone.f (interpS Θ) (fst (fst y)) , snd (fst y)) , snd y)
               ((Monotone.is-monotone (interpS Θ) (fst (fst x)) (fst (fst y)) (fst (fst x₁)) ,
               snd (fst x₁)) ,
               snd x₁)))
        (k , Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
          (λ x → subst-eq-l Θ e₁ x)
          (λ x →
            Preorder-str.trans (snd [ τ ]t)
              (Monotone.f (interpE (subst e₂ (s-extend (s-extend Θ)))) x)
              (Monotone.f (interpE e₂) (Monotone.f (interpS {nat :: τ :: Γ} {_ :: _ :: Γ'} (s-extend (s-extend Θ))) x))
              (Monotone.f (interpE e₂) ((Monotone.f (interpS Θ) (fst (fst x)) , snd (fst x)) , snd x))
                (subst-eq-l (s-extend (s-extend Θ)) e₂ x)
                (Monotone.is-monotone (interpE e₂)
                  (Monotone.f (interpS {nat :: τ :: Γ} {_ :: _ :: Γ'} (s-extend (s-extend Θ))) x)
                  ((Monotone.f (interpS Θ) (fst (fst x)) , snd (fst x)) , snd x)
                    (((Preorder-str.trans (snd [ Γ' ]c)
                      (Monotone.f (interpS (λ x₁ → ren (ren (Θ x₁) iS) iS)) x)
                      (Monotone.f (interpS (λ x₁ → ren (Θ x₁) iS)) (fst x))
                      (Monotone.f (interpS Θ) (fst (fst x)))
                        (subst-eq-l-lam {τ :: Γ} {Γ'} (λ x₁ → ren (Θ x₁) iS) (fst x) (snd x))
                        (subst-eq-l-lam Θ (fst (fst x)) (snd (fst x)))) ,
                    (Preorder-str.refl (snd [ τ ]t) (snd (fst x)))) ,
                    (♭nat-refl (snd x))))))
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
{-  subst-eq-l Θ rz k = <>
  subst-eq-l Θ (rsuc e) k = subst-eq-l Θ e k
  subst-eq-l {Γ} {Γ'} {τ} Θ (rrec e e₁ e₂ P) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (comp (pair' id (interpE (subst e Θ)))
        (rec' (interpE (subst e₁ Θ)) (unlam' (unlam' (interpE (subst e₂ Θ))))
        (sound (subst e₁ Θ) (app (app (subst e₂ Θ) rz) (subst e₁ Θ)) (subst-cong P)))) k)
      (Monotone.f (rec' (interpE (subst e₁ Θ)) (unlam' (unlam' (interpE (subst e₂ Θ))))
        (λ x₁ → sound (subst e₁ Θ) (app (app (subst e₂ Θ) rz) (subst e₁ Θ)) (subst-cong P) x₁))
        (k , Monotone.f (interpE e) (Monotone.f (interpS Θ) k)))
      (Monotone.f (comp (pair' id (interpE e))
        (rec' (interpE e₁) (unlam' (unlam' (interpE e₂)))
        (sound e₁ (app (app e₂ rz) e₁) P))) (Monotone.f (interpS Θ) k))
      (h-lem2 (interpE (subst e₁ Θ)) (unlam' (unlam' (interpE (subst e₂ Θ))))
        (k , Monotone.f (interpE (subst e Θ)) k)
        (k , Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
        (λ x → sound (subst e₁ Θ) (app (app (subst e₂ Θ) rz) (subst e₁ Θ)) (subst-cong P) x)
        (subst-eq-l Θ e k))
      (h-cong2
        (interpE (subst e₁ Θ))
        (monotone (λ x → Monotone.f (interpE e₁) (Monotone.f (interpS Θ) x))
          (λ x y x₁ →
             Monotone.is-monotone (interpE e₁)
               (Monotone.f (interpS Θ) x)
               (Monotone.f (interpS Θ) y)
                 (Monotone.is-monotone (interpS Θ) x y x₁)))
        (unlam' (unlam' (interpE (subst e₂ Θ))))
        (monotone (λ x → Monotone.f (Monotone.f (Monotone.f (interpE e₂) (Monotone.f (interpS Θ) (fst (fst x)))) (snd (fst x))) (snd x))
          (λ x y x₁ →
            Monotone.is-monotone (unlam' (unlam' (interpE e₂)))
              ((Monotone.f (interpS Θ) (fst (fst x)) , snd (fst x)) , snd x)
              ((Monotone.f (interpS Θ) (fst (fst y)) , snd (fst y)) , snd y)
                ((Monotone.is-monotone (interpS Θ) (fst (fst x)) (fst (fst y)) (fst (fst x₁)) , snd (fst x₁)) , snd x₁)))
        (λ x → subst-eq-l Θ e₁ x)
        (λ x → subst-eq-l Θ e₂ (fst (fst x)) (snd (fst x)) (snd x))
        (λ x₁ → sound (subst e₁ Θ) (app (app (subst e₂ Θ) rz) (subst e₁ Θ)) (subst-cong P) x₁)
        (λ x₁ → sound e₁ (app (app e₂ rz) e₁) P (Monotone.f (interpS Θ) x₁))
        (k , Monotone.f (interpE e) (Monotone.f (interpS Θ) k)))-}
  subst-eq-l Θ (prod e e₁) k = (subst-eq-l Θ e k) , (subst-eq-l Θ e₁ k)
  subst-eq-l Θ (l-proj e) k = fst (subst-eq-l Θ e k)
  subst-eq-l Θ (r-proj e) k = snd (subst-eq-l Θ e k)
  subst-eq-l Θ nil k = <>
  subst-eq-l Θ (e ::c e₁) k = (subst-eq-l Θ e k) , (subst-eq-l Θ e₁ k)
  subst-eq-l {Γ} {Γ'} {τ} Θ (listrec {.Γ'} {τ'} e e₁ e₂) k =
    Preorder-str.trans (snd [ τ ]t)
      (lrec (Monotone.f (interpE (subst e Θ)) k)
        (Monotone.f (interpE (subst e₁ Θ)) k)
        (λ x₁ x₂ x₃ → Monotone.f (interpE (subst e₂ (s-extend (s-extend (s-extend Θ))))) (((k , x₃) , x₂) , x₁)))
      (lrec (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
        (Monotone.f (interpE (subst e₁ Θ)) k)
        (λ x₁ x₂ x₃ → Monotone.f (interpE (subst e₂ (s-extend (s-extend (s-extend Θ))))) (((k , x₃) , x₂) , x₁)))
      (lrec (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
        (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k))
        (λ x₁ x₂ x₃ → Monotone.f (interpE e₂) (((Monotone.f (interpS Θ) k , x₃) , x₂) , x₁)))
      (listrec-fix-args (interpE (subst e₁ Θ)) (interpE (subst e₂ (s-extend (s-extend (s-extend Θ)))))
        (k , Monotone.f (interpE (subst e Θ)) k)
        (k , Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
          (Preorder-str.refl (snd [ Γ ]c) k , subst-eq-l Θ e k))
      (lrec-cong
        (interpE (subst e₁ Θ))
        (monotone (λ k₁ → Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k₁))
          (λ x y x₁ → Monotone.is-monotone (interpE e₁) (Monotone.f (interpS Θ) x) (Monotone.f (interpS Θ) y) (Monotone.is-monotone (interpS Θ) x y x₁)))
        (interpE (subst e₂ (s-extend (s-extend (s-extend Θ)))))
        (monotone (λ x → Monotone.f (interpE e₂) (((Monotone.f (interpS Θ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₂)
              (((Monotone.f (interpS Θ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x)
              (((Monotone.f (interpS Θ) (fst (fst (fst y))) , snd (fst (fst y))) , snd (fst y)) , snd y)
              (((Monotone.is-monotone (interpS Θ) (fst (fst (fst x))) (fst (fst (fst y))) (fst (fst (fst x₁))) ,
                snd (fst (fst x₁))) ,
                snd (fst x₁)) ,
                snd x₁)))
         (k , Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
           (λ x → subst-eq-l Θ e₁ x)
           (λ x →
             Preorder-str.trans (snd [ τ ]t)
               (Monotone.f (interpE (subst e₂ (s-extend (s-extend (s-extend Θ))))) x)
               (Monotone.f (interpE e₂) (Monotone.f (interpS {τ' :: list τ' :: τ :: Γ} {_ :: _ :: _ :: Γ'} (s-extend (s-extend (s-extend Θ)))) x))
               (Monotone.f (interpE e₂) (((Monotone.f (interpS Θ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x))
                 (subst-eq-l (s-extend (s-extend (s-extend Θ))) e₂ x)
                 (Monotone.is-monotone (interpE e₂)
                   (Monotone.f (interpS {τ' :: list τ' :: τ :: Γ} {_ :: _ :: _ :: Γ'} (s-extend (s-extend (s-extend Θ)))) x)
                   (((Monotone.f (interpS Θ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x)
                     ((((Preorder-str.trans (snd [ Γ' ]c)
                       (Monotone.f (interpS (λ x₁ → ren (ren (ren (Θ x₁) iS) iS) iS)) x)
                       (Monotone.f (interpS {τ :: Γ} {Γ'} (throw-s (s-extend Θ))) (fst (fst x)))
                       (Monotone.f (interpS Θ) (fst (fst (fst x))))
                         (Preorder-str.trans (snd [ Γ' ]c)
                           (Monotone.f (interpS (λ x₁ → ren (ren (ren (Θ x₁) iS) iS) iS)) x)
                           (Monotone.f (interpS (λ x₁ → ren (ren (Θ x₁) iS) iS)) (fst x))
                           (Monotone.f (interpS {τ :: Γ} {Γ'} (throw-s (s-extend Θ))) (fst (fst x)))
                             (subst-eq-l-lam (λ x₁ → ren (ren (Θ x₁) iS) iS) (fst x) (snd x))
                             (subst-eq-l-lam (λ x₁ → ren (Θ x₁) iS) (fst (fst x)) (snd (fst x))))
                         (subst-eq-l-lam {Γ} {Γ'} Θ (fst (fst (fst x))) (snd (fst (fst x))))) ,
                     (Preorder-str.refl (snd [ τ ]t) (snd (fst (fst x))))) ,
                     (l-refl (snd [ τ' ]t) (snd (fst x)))) ,
                     (Preorder-str.refl (snd [ τ' ]t) (snd x))))))
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
  subst-eq-r {Γ} {Γ'} {τ} Θ (rec e e₁ e₂) k =
    Preorder-str.trans (snd [ τ ]t)
      (natrec (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k))
        (λ n x₂ → Monotone.f (interpE e₂) ((Monotone.f (interpS Θ) k , x₂) , n))
        (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)))
      (natrec (Monotone.f (interpE (subst e₁ Θ)) k)
        (λ n x₂ → Monotone.f (interpE (subst e₂ (s-extend (s-extend Θ)))) ((k , x₂) , n))
        (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)))
      (natrec (Monotone.f (interpE (subst e₁ Θ)) k)
        (λ n x₂ → Monotone.f (interpE (subst e₂ (s-extend (s-extend Θ)))) ((k , x₂) , n))
        (Monotone.f (interpE (subst e Θ)) k))
      (♭h-cong
        (monotone (λ v → Monotone.f (interpE e₁) (Monotone.f (interpS Θ) v))
          (λ x y x₁ → Monotone.is-monotone (interpE e₁) (Monotone.f (interpS Θ) x) (Monotone.f (interpS Θ) y) (Monotone.is-monotone (interpS Θ) x y x₁)))
        (interpE (subst e₁ Θ))
        (monotone (λ v → Monotone.f (interpE e₂) ((Monotone.f (interpS Θ) (fst (fst v)) , snd (fst v)) , snd v))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₂)
              ((Monotone.f (interpS Θ) (fst (fst x)) , snd (fst x)) , snd x)
              ((Monotone.f (interpS Θ) (fst (fst y)) , snd (fst y)) , snd y)
                ((Monotone.is-monotone (interpS Θ) (fst (fst x)) (fst (fst y)) (fst (fst x₁)) ,
                snd (fst x₁)) ,
                snd x₁)))
         (interpE (subst e₂ (s-extend (s-extend Θ))))
         (k , (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)))
           (λ x → subst-eq-r Θ e₁ x)
           (λ x →
             Preorder-str.trans (snd [ τ ]t)
               (Monotone.f (interpE e₂) ((Monotone.f (interpS Θ) (fst (fst x)) , snd (fst x)) , snd x))
               (Monotone.f (interpE e₂) (Monotone.f (interpS {nat :: τ :: Γ} {_ :: _ :: Γ'} (s-extend (s-extend Θ))) x))
               (Monotone.f (interpE (subst e₂ (s-extend (s-extend Θ)))) x)
                 (Monotone.is-monotone (interpE e₂)
                   ((Monotone.f (interpS Θ) (fst (fst x)) , snd (fst x)) , snd x)
                   (Monotone.f (interpS {nat :: τ :: Γ} {_ :: _ :: Γ'} (s-extend (s-extend Θ))) x)
                     (((Preorder-str.trans (snd [ Γ' ]c)
                       (Monotone.f (interpS Θ) (fst (fst x)))
                       (Monotone.f (interpS (λ x₁ → ren (Θ x₁) iS)) (fst x))
                       (Monotone.f (interpS (λ x₁ → ren (ren (Θ x₁) iS) iS)) x)
                         (subst-eq-r-lam Θ (fst (fst x)) (snd (fst x)))
                         (subst-eq-r-lam {τ :: Γ} {Γ'} (λ x₁ → ren (Θ x₁) iS) (fst x) (snd x))) ,
                     (Preorder-str.refl (snd [ τ ]t) (snd (fst x)))) ,
                     (♭nat-refl (snd x))))
                 (subst-eq-r (s-extend (s-extend Θ)) e₂ x)))
      (♭h-fix-args (interpE (subst e₁ Θ))
        (interpE (subst e₂ (s-extend (s-extend Θ))))
        (k , Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
        (k , Monotone.f (interpE (subst e Θ)) k)
          (subst-eq-r Θ e k))
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
{-  subst-eq-r Θ rz k = <>
  subst-eq-r Θ (rsuc e) k = subst-eq-r Θ e k
  subst-eq-r {Γ} {Γ'} {τ} Θ (rrec e e₁ e₂ P) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (comp (pair' id (interpE e))
        (rec' (interpE e₁) (unlam' (unlam' (interpE e₂)))
        (sound e₁ (app (app e₂ rz) e₁) P))) (Monotone.f (interpS Θ) k))
      (Monotone.f (rec' (interpE (subst e₁ Θ)) (unlam' (unlam' (interpE (subst e₂ Θ))))
        (λ x₁ → sound (subst e₁ Θ) (app (app (subst e₂ Θ) rz) (subst e₁ Θ)) (subst-cong P) x₁))
        (k , Monotone.f (interpE e) (Monotone.f (interpS Θ) k)))
      (Monotone.f (comp (pair' id (interpE (subst e Θ)))
        (rec' (interpE (subst e₁ Θ)) (unlam' (unlam' (interpE (subst e₂ Θ))))
        (sound (subst e₁ Θ) (app (app (subst e₂ Θ) rz) (subst e₁ Θ)) (subst-cong P)))) k)
      (h-cong2
        (monotone (λ z₁ → Monotone.f (interpE e₁) (Monotone.f (interpS Θ) z₁))
          (λ x y x₁ →
            Monotone.is-monotone (interpE e₁)
              (Monotone.f (interpS Θ) x)
              (Monotone.f (interpS Θ) y)
                (Monotone.is-monotone (interpS Θ) x y x₁)))
        (interpE (subst e₁ Θ))
        (monotone (λ v → Monotone.f (Monotone.f (Monotone.f (interpE e₂) (Monotone.f (interpS Θ) (fst (fst v)))) (snd (fst v))) (snd v))
          (λ x y x₁ →
            Monotone.is-monotone (unlam' (unlam' (interpE e₂)))
              ((Monotone.f (interpS Θ) (fst (fst x)) , snd (fst x)) , snd x)
              ((Monotone.f (interpS Θ) (fst (fst y)) , snd (fst y)) , snd y)
                ((Monotone.is-monotone (interpS Θ) (fst (fst x)) (fst (fst y)) (fst (fst x₁)) , snd (fst x₁)) , snd x₁)))
        (unlam' (unlam' (interpE (subst e₂ Θ))))
        (λ x → subst-eq-r Θ e₁ x)
        (λ x → subst-eq-r Θ e₂ (fst (fst x)) (snd (fst x)) (snd x))
        (λ x₁ → sound e₁ (app (app e₂ rz) e₁) P (Monotone.f (interpS Θ) x₁))
        (λ x₁ → sound (subst e₁ Θ) (app (app (subst e₂ Θ) rz) (subst e₁ Θ)) (subst-cong P) x₁)
        (k , (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))))
      (h-lem2 (interpE (subst e₁ Θ)) (unlam' (unlam' (interpE (subst e₂ Θ))))
        (k , Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
        (k , Monotone.f (interpE (subst e Θ)) k)
        (λ x → sound (subst e₁ Θ) (app (app (subst e₂ Θ) rz) (subst e₁ Θ)) (subst-cong P) x)
        (subst-eq-r Θ e k))-}
  subst-eq-r Θ (prod e e₁) k = (subst-eq-r Θ e k) , (subst-eq-r Θ e₁ k)
  subst-eq-r Θ (l-proj e) k = fst (subst-eq-r Θ e k)
  subst-eq-r Θ (r-proj e) k = snd (subst-eq-r Θ e k)
  subst-eq-r Θ nil k = <>
  subst-eq-r Θ (e ::c e₁) k = (subst-eq-r Θ e k) , (subst-eq-r Θ e₁ k)
  subst-eq-r {Γ} {Γ'} {τ} Θ (listrec {.Γ'} {τ'} e e₁ e₂) k =
    Preorder-str.trans (snd [ τ ]t)
    (lrec (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
      (Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k))
      (λ x₁ x₂ x₃ → Monotone.f (interpE e₂) (((Monotone.f (interpS Θ) k , x₃) , x₂) , x₁)))
    (lrec (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
      (Monotone.f (interpE (subst e₁ Θ)) k)
      (λ x₁ x₂ x₃ → Monotone.f (interpE (subst e₂ (s-extend (s-extend (s-extend Θ))))) (((k , x₃) , x₂) , x₁)))
    (lrec (Monotone.f (interpE (subst e Θ)) k)
      (Monotone.f (interpE (subst e₁ Θ)) k)
      (λ x₁ x₂ x₃ → Monotone.f (interpE (subst e₂ (s-extend (s-extend (s-extend Θ))))) (((k , x₃) , x₂) , x₁)))
    (lrec-cong
      (monotone (λ k₁ → Monotone.f (interpE e₁) (Monotone.f (interpS Θ) k₁))
        (λ x y x₁ → Monotone.is-monotone (interpE e₁) (Monotone.f (interpS Θ) x) (Monotone.f (interpS Θ) y) (Monotone.is-monotone (interpS Θ) x y x₁)))
      (interpE (subst e₁ Θ))
      (monotone (λ x → Monotone.f (interpE e₂) (((Monotone.f (interpS Θ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x))
        (λ x y x₁ →
          Monotone.is-monotone (interpE e₂)
            (((Monotone.f (interpS Θ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x)
            (((Monotone.f (interpS Θ) (fst (fst (fst y))) , snd (fst (fst y))) , snd (fst y)) , snd y)
              (((Monotone.is-monotone (interpS Θ)
                (fst (fst (fst x))) (fst (fst (fst y))) (fst (fst (fst x₁))) , snd (fst (fst x₁))) , snd (fst x₁)) , snd x₁)))
       (interpE (subst e₂ (s-extend (s-extend (s-extend Θ)))))
       (k , (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)))
         (λ x → subst-eq-r Θ e₁ x)
         (λ x →
           Preorder-str.trans (snd [ τ ]t)
             (Monotone.f (interpE e₂) (((Monotone.f (interpS Θ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x))
             (Monotone.f (interpE e₂) (Monotone.f (interpS {τ' :: list τ' :: τ :: Γ} {_ :: _ :: _ :: Γ'} (s-extend (s-extend (s-extend Θ)))) x))
             (Monotone.f (interpE (subst e₂ (s-extend (s-extend (s-extend Θ))))) x)
               (Monotone.is-monotone (interpE e₂)
                 (((Monotone.f (interpS Θ) (fst (fst (fst x))) , snd (fst (fst x))) , snd (fst x)) , snd x)
                 (Monotone.f (interpS {τ' :: list τ' :: τ :: Γ} {_ :: _ :: _ :: Γ'} (s-extend (s-extend (s-extend Θ)))) x)
                   ((((Preorder-str.trans (snd [ Γ' ]c)
                     (Monotone.f (interpS Θ) (fst (fst (fst x))))
                     (Monotone.f (interpS {τ :: Γ} {Γ'} (throw-s (s-extend Θ))) (fst (fst x)))
                     (Monotone.f (interpS (λ x₁ → ren (ren (ren (Θ x₁) iS) iS) iS)) x)
                       (subst-eq-r-lam {Γ} {Γ'} Θ (fst (fst (fst x))) (snd (fst (fst x))))
                       (Preorder-str.trans (snd [ Γ' ]c)
                         (Monotone.f (interpS {τ :: Γ} {Γ'} (throw-s (s-extend Θ))) (fst (fst x)))
                         (Monotone.f (interpS (λ x₁ → ren (ren (Θ x₁) iS) iS)) (fst x))
                         (Monotone.f (interpS (λ x₁ → ren (ren (ren (Θ x₁) iS) iS) iS)) x)
                           (subst-eq-r-lam (λ x₁ → ren (Θ x₁) iS) (fst (fst x)) (snd (fst x)))
                           (subst-eq-r-lam (λ x₁ → ren (ren (Θ x₁) iS) iS) (fst x) (snd x)))) ,
                   (Preorder-str.refl (snd [ τ ]t) (snd (fst (fst x))))) ,
                   (l-refl (snd [ τ' ]t) (snd (fst x)))) ,
                   (Preorder-str.refl (snd [ τ' ]t) (snd x))))
               (subst-eq-r (s-extend (s-extend (s-extend Θ))) e₂ x)))
    (listrec-fix-args (interpE (subst e₁ Θ)) (interpE (subst e₂ (s-extend (s-extend (s-extend Θ)))))
      (k , Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
      (k , Monotone.f (interpE (subst e Θ)) k)
        (Preorder-str.refl (snd [ Γ ]c) k , subst-eq-r Θ e k))
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

  interp-rr-l : ∀ {Γ Γ' Γ''} (ρ1 : rctx Γ Γ') (ρ2 : rctx Γ' Γ'') (k : fst [ Γ ]c)
              → Preorder-str.≤ (snd [ Γ'' ]c)
                (Monotone.f (interpR ρ2) (Monotone.f (interpR ρ1) k))
                (Monotone.f (interpR (λ x → ρ1 (ρ2 x))) k)
  interp-rr-l {Γ'' = []} ρ1 ρ2 k = <>
  interp-rr-l {Γ'' = x :: Γ''} ρ1 ρ2 k = (interp-rr-l ρ1 (throw-r ρ2) k) , (ren-eq-r ρ1 (var (ρ2 i0)) k)

  interp-rr-r : ∀ {Γ Γ' Γ''} (ρ1 : rctx Γ Γ') (ρ2 : rctx Γ' Γ'') (k : fst [ Γ ]c)
              → Preorder-str.≤ (snd [ Γ'' ]c)
                (Monotone.f (interpR (λ x → ρ1 (ρ2 x))) k)
                (Monotone.f (interpR ρ2) (Monotone.f (interpR ρ1) k))
  interp-rr-r {Γ'' = []} ρ1 ρ2 k = <>
  interp-rr-r {Γ'' = x :: Γ''} ρ1 ρ2 k = (interp-rr-r ρ1 (throw-r ρ2) k) , (ren-eq-l ρ1 (var (ρ2 i0)) k)

  interp-rs-l : ∀ {Γ Γ' Γ''} (ρ : rctx Γ Γ') (Θ : sctx Γ' Γ'') (k : fst [ Γ ]c)
              → Preorder-str.≤ (snd [ Γ'' ]c)
                (Monotone.f (interpS Θ) (Monotone.f (interpR ρ) k))
                (Monotone.f (interpS (λ x → ren (Θ x) ρ)) k)
  interp-rs-l {Γ'' = []} ρ Θ k = <>
  interp-rs-l {Γ'' = x :: Γ''} ρ Θ k = (interp-rs-l ρ (throw-s Θ) k) , (ren-eq-r ρ (Θ i0) k)

  interp-rs-r : ∀ {Γ Γ' Γ''} (ρ : rctx Γ Γ') (Θ : sctx Γ' Γ'') (k : fst [ Γ ]c)
              → Preorder-str.≤ (snd [ Γ'' ]c)
                (Monotone.f (interpS (λ x → ren (Θ x) ρ)) k)
                (Monotone.f (interpS Θ) (Monotone.f (interpR ρ) k))
  interp-rs-r {Γ'' = []} ρ Θ k = <>
  interp-rs-r {Γ'' = x :: Γ''} ρ Θ k = (interp-rs-r ρ (throw-s Θ) k) , (ren-eq-l ρ (Θ i0) k)

  interp-sr-l : ∀ {Γ Γ' Γ''} (Θ : sctx Γ Γ') (ρ : rctx Γ' Γ'') (k : fst [ Γ ]c)
              → Preorder-str.≤ (snd [ Γ'' ]c)
                (Monotone.f (interpR ρ) (Monotone.f (interpS Θ) k))
                (Monotone.f (interpS (λ x → Θ (ρ x))) k)
  interp-sr-l {Γ'' = []} Θ ρ k = <>
  interp-sr-l {Γ'' = x :: Γ''} Θ ρ k = (interp-sr-l Θ (throw-r ρ) k) , (subst-eq-r Θ (var (ρ i0)) k)

  interp-sr-r : ∀ {Γ Γ' Γ''} (Θ : sctx Γ Γ') (ρ : rctx Γ' Γ'') (k : fst [ Γ ]c)
              → Preorder-str.≤ (snd [ Γ'' ]c)
                (Monotone.f (interpS (λ x → Θ (ρ x))) k)
                (Monotone.f (interpR ρ) (Monotone.f (interpS Θ) k))
  interp-sr-r {Γ'' = []} Θ ρ k = <>
  interp-sr-r {Γ'' = x :: Γ''} Θ ρ k = (interp-sr-r Θ (throw-r ρ) k) , (subst-eq-l Θ (var (ρ i0)) k)

  interp-ss-l : ∀ {Γ Γ' Γ''} (Θ1 : sctx Γ Γ') (Θ2 : sctx Γ' Γ'') (k : fst [ Γ ]c)
              → Preorder-str.≤ (snd [ Γ'' ]c)
                (Monotone.f (interpS (λ x → subst (Θ2 x) Θ1)) k)
                (Monotone.f (interpS Θ2) (Monotone.f (interpS Θ1) k))
  interp-ss-l {Γ'' = []} Θ1 Θ2 k = <>
  interp-ss-l {Γ'' = x :: Γ''} Θ1 Θ2 k = (interp-ss-l Θ1 (throw-s Θ2) k) , (subst-eq-l Θ1 (Θ2 i0) k)

  interp-ss-r : ∀ {Γ Γ' Γ''} (Θ1 : sctx Γ Γ') (Θ2 : sctx Γ' Γ'') (k : fst [ Γ ]c)
              → Preorder-str.≤ (snd [ Γ'' ]c)
                (Monotone.f (interpS Θ2) (Monotone.f (interpS Θ1) k))
                (Monotone.f (interpS (λ x → subst (Θ2 x) Θ1)) k)
  interp-ss-r {Γ'' = []} Θ1 Θ2 k = <>
  interp-ss-r {Γ'' = x :: Γ''} Θ1 Θ2 k = (interp-ss-r Θ1 (throw-s Θ2) k) , (subst-eq-r Θ1 (Θ2 i0) k)

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

  lam-s-lem-r : ∀ {Γ} (k : fst [ Γ ]c) → Preorder-str.≤ (snd [ Γ ]c) k (Monotone.f (interpS {Γ} {Γ} ids) k)
  lam-s-lem-r {[]} k = <>
  lam-s-lem-r {x :: Γ} (k1 , k2) =
    (Preorder-str.trans (snd [ Γ ]c)
      k1 
      (Monotone.f (interpS {Γ} {Γ} ids) k1)
      (Monotone.f (interpS {x :: Γ} {Γ} (throw-s ids)) (k1 , k2))
      (lam-s-lem-r {Γ} k1)
      (subst-eq-r-lam {Γ} {Γ} ids k1 (Monotone.f (interpE {x :: Γ} {x} (ids i0)) (k1 , k2)))) , 
    (Preorder-str.refl (snd [ x ]t) k2)

  interp-subst-comp-l : ∀ {Γ Γ' τ'} (Θ : sctx Γ Γ') (v : Γ |- τ') (k : fst [ Γ ]c)
                      → Preorder-str.≤ (snd [ Γ' ]c)
                        (Monotone.f (interpS (λ x → subst (ren (Θ x) iS) (lem3' ids v))) k)
                        (Monotone.f (interpS (λ x → Θ x)) k)
  interp-subst-comp-l {Γ' = []} Θ v k = <>
  interp-subst-comp-l {Γ} {Γ' = x :: Γ'} {τ'} Θ v k =
    (interp-subst-comp-l (throw-s Θ) v k) ,
    (Preorder-str.trans (snd [ x ]t)
      (Monotone.f (interpE (subst (ren (Θ i0) iS) (lem3' ids v))) k)
      (Monotone.f (interpE (ren (Θ i0) iS)) (Monotone.f (interpS (lem3' ids v)) k))
      (Monotone.f (interpE (Θ i0)) k)
      (subst-eq-l (lem3' ids v) (ren (Θ i0) iS) k)
      (Preorder-str.trans (snd [ x ]t)
        (Monotone.f (interpE (ren (Θ i0) iS)) (Monotone.f (interpS (lem3' ids v)) k))
        (Monotone.f (interpE (Θ i0)) (Monotone.f (interpR {τ' :: Γ} {Γ} iS) (Monotone.f (interpS {Γ} {τ' :: Γ} (lem3' ids v)) k)))
        (Monotone.f (interpE (Θ i0)) k)
        (ren-eq-l iS (Θ i0) (Monotone.f (interpS (lem3' ids v)) k))
        (Monotone.is-monotone (interpE (Θ i0))
          (Monotone.f (interpR {τ' :: Γ} {Γ} iS) (Monotone.f (interpS {Γ} {τ' :: Γ} (lem3' ids v)) k))
          k
          (Preorder-str.trans (snd [ Γ ]c)
            (Monotone.f (interpR {τ' :: Γ} {Γ} iS) (Monotone.f (interpS {Γ} {τ' :: Γ} (lem3' ids v)) k))
            (Monotone.f (interpR {Γ} {Γ} (λ x₂ → x₂)) k)
            k
            (Preorder-str.trans (snd [ Γ ]c)
               (Monotone.f (interpR {τ' :: Γ} {Γ} iS) (Monotone.f (interpS {Γ} {τ' :: Γ} (lem3' ids v)) k))
               (Monotone.f (interpR {τ' :: Γ} {Γ} iS) (k , Monotone.f (interpE v) k))
               (Monotone.f (interpR {Γ} {Γ} (λ x₂ → x₂)) k)
               (Monotone.is-monotone (interpR {τ' :: Γ} {Γ} iS)
                 (Monotone.f (interpS {Γ} {τ' :: Γ} (lem3' ids v)) k)
                 (k , Monotone.f (interpE v) k)
                   (lam-s-lem {Γ} k , (Preorder-str.refl (snd [ τ' ]t) (Monotone.f (interpE v) k))))
               (ren-eq-l-lam {Γ} {Γ} {τ'} (λ x₂ → x₂) k (Monotone.f (interpE v) k)))
            (ids-lem-l {Γ} k)))))

  interp-subst-comp-r : ∀ {Γ Γ' τ'} (Θ : sctx Γ Γ') (v : Γ |- τ') (k : fst [ Γ ]c)
                      → Preorder-str.≤ (snd [ Γ' ]c)
                        (Monotone.f (interpS (λ x → Θ x)) k)
                        (Monotone.f (interpS (λ x → subst (ren (Θ x) iS) (lem3' ids v))) k)
  interp-subst-comp-r {Γ' = []} Θ v k = <>
  interp-subst-comp-r {Γ} {Γ' = x :: Γ'} {τ'} Θ v k =
    (interp-subst-comp-r (throw-s Θ) v k) ,
    Preorder-str.trans (snd [ x ]t)
      (Monotone.f (interpE (Θ i0)) k)
      (Monotone.f (interpE (ren (Θ i0) iS)) (Monotone.f (interpS (lem3' ids v)) k))
      (Monotone.f (interpE (subst (ren (Θ i0) iS) (lem3' ids v))) k)
      (Preorder-str.trans (snd [ x ]t)
        (Monotone.f (interpE (Θ i0)) k)
        (Monotone.f (interpE (Θ i0)) (Monotone.f (interpR {τ' :: Γ} {Γ} iS) (Monotone.f (interpS {Γ} {τ' :: Γ} (lem3' ids v)) k)))
        (Monotone.f (interpE (ren (Θ i0) iS)) (Monotone.f (interpS (lem3' ids v)) k))
        (Monotone.is-monotone (interpE (Θ i0))
          k
          (Monotone.f (interpR {τ' :: Γ} {Γ} iS) (Monotone.f (interpS {Γ} {τ' :: Γ} (lem3' ids v)) k))
          (Preorder-str.trans (snd [ Γ ]c)
            k
            (Monotone.f (interpR {Γ} {Γ} (λ x₂ → x₂)) k)
            (Monotone.f (interpR {τ' :: Γ} {Γ} iS) (Monotone.f (interpS {Γ} {τ' :: Γ} (lem3' ids v)) k))
            (ids-lem-r {Γ} k)
            (Preorder-str.trans (snd [ Γ ]c)
              (Monotone.f (interpR {Γ} {Γ} (λ x₂ → x₂)) k)
              (Monotone.f (interpR {τ' :: Γ} {Γ} iS) (k , Monotone.f (interpE v) k))
              (Monotone.f (interpR {τ' :: Γ} {Γ} iS) (Monotone.f (interpS {Γ} {τ' :: Γ} (lem3' ids v)) k))
              (ren-eq-r-lam {Γ} {Γ} {τ'} (λ x₂ → x₂) k (Monotone.f (interpE v) k))
              (Monotone.is-monotone (interpR {τ' :: Γ} {Γ} iS)
                (k , Monotone.f (interpE v) k)
                (Monotone.f (interpS {Γ} {τ' :: Γ} (lem3' ids v)) k)
                  (lam-s-lem-r {Γ} k , Preorder-str.refl (snd [ τ' ]t) (Monotone.f (interpE v) k))))))
        (ren-eq-r iS (Θ i0) (Monotone.f (interpS (lem3' ids v)) k)))
      (subst-eq-r (lem3' ids v) (ren (Θ i0) iS) k)

  sound : ∀ {Γ τ} (e e' : Γ |- τ) → e ≤s e' → PREORDER≤ ([ Γ ]c ->p [ τ ]t) (interpE e) (interpE e')
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
  sound ._ ._ (subst-cong2 x) k = {!!}
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
  sound {Γ} {τ} .(ren (ren e ρ2) ρ1) ._ (ren-comp-l ρ1 ρ2 e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (ren (ren e ρ2) ρ1)) k)
      (Monotone.f (interpE (ren e ρ2)) (Monotone.f (interpR ρ1) k))
      (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k)
      (ren-eq-l ρ1 (ren e ρ2) k)
      (Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE (ren e ρ2)) (Monotone.f (interpR ρ1) k))
        (Monotone.f (interpE e) (Monotone.f (interpR (ρ1 ∙rr ρ2)) k))
        (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (ren e ρ2)) (Monotone.f (interpR ρ1) k))
          (Monotone.f (interpE e) (Monotone.f (interpR ρ2) (Monotone.f (interpR ρ1) k)))
          (Monotone.f (interpE e) (Monotone.f (interpR (ρ1 ∙rr ρ2)) k))
          (ren-eq-l ρ2 e (Monotone.f (interpR ρ1) k))
          (Monotone.is-monotone (interpE e)
            (Monotone.f (interpR ρ2) (Monotone.f (interpR ρ1) k))
            (Monotone.f (interpR (ρ1 ∙rr ρ2)) k)
            (interp-rr-l ρ1 ρ2 k)))
        (ren-eq-r (ρ1 ∙rr ρ2) e k))
  sound {Γ} {τ} ._ .(ren (ren e ρ2) ρ1) (ren-comp-r ρ1 ρ2 e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k)
      (Monotone.f (interpE (ren e ρ2)) (Monotone.f (interpR ρ1) k))
      (Monotone.f (interpE (ren (ren e ρ2) ρ1)) k)
      (Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k)
        (Monotone.f (interpE e) (Monotone.f (interpR (ρ1 ∙rr ρ2)) k))
        (Monotone.f (interpE (ren e ρ2)) (Monotone.f (interpR ρ1) k))
        (ren-eq-l (ρ1 ∙rr ρ2) e k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE e) (Monotone.f (interpR (ρ1 ∙rr ρ2)) k))
          (Monotone.f (interpE e) (Monotone.f (interpR ρ2) (Monotone.f (interpR ρ1) k)))
          (Monotone.f (interpE (ren e ρ2)) (Monotone.f (interpR ρ1) k))
          (Monotone.is-monotone (interpE e)
            (Monotone.f (interpR (ρ1 ∙rr ρ2)) k)
            (Monotone.f (interpR ρ2) (Monotone.f (interpR ρ1) k))
              (interp-rr-r ρ1 ρ2 k))
          (ren-eq-r ρ2 e (Monotone.f (interpR ρ1) k))))
      (ren-eq-r ρ1 (ren e ρ2) k)
  sound {Γ} {τ} e ._ (subst-id-l .e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE e) k)
      (Monotone.f (interpE e) (Monotone.f (interpS {Γ} {Γ} ids) k))
      (Monotone.f (interpE (subst e ids)) k)
      (Monotone.is-monotone (interpE e) k (Monotone.f (interpS {Γ} {Γ} ids) k) (lam-s-lem-r {Γ} k))
      (subst-eq-r ids e k)
  sound {Γ} {τ} ._ e' (subst-id-r .e') k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e' ids)) k)
      (Monotone.f (interpE e') (Monotone.f (interpS {Γ} {Γ} ids) k))
      (Monotone.f (interpE e') k)
      (subst-eq-l ids e' k)
      (Monotone.is-monotone (interpE e') (Monotone.f (interpS {Γ} {Γ} ids) k) k (lam-s-lem {Γ} k))
  sound {Γ} {τ} .(ren (subst e Θ) ρ) ._ (subst-rs-l ρ Θ e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (ren (subst e Θ) ρ)) k)
      (Monotone.f (interpE (subst e Θ)) (Monotone.f (interpR ρ) k))
      (Monotone.f (interpE (subst e (ρ rs Θ))) k)
      (ren-eq-l ρ (subst e Θ) k)
      (Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE (subst e Θ)) (Monotone.f (interpR ρ) k))
        (Monotone.f (interpE e) (Monotone.f (interpS Θ) (Monotone.f (interpR ρ) k)))
        (Monotone.f (interpE (subst e (ρ rs Θ))) k)
        (subst-eq-l Θ e (Monotone.f (interpR ρ) k))
        (Preorder-str.trans (snd [ τ ]t)
           (Monotone.f (interpE e) (Monotone.f (interpS Θ) (Monotone.f (interpR ρ) k)))
           (Monotone.f (interpE e) (Monotone.f (interpS (ρ rs Θ)) k))
           (Monotone.f (interpE (subst e (ρ rs Θ))) k)
           (Monotone.is-monotone (interpE e)
             (Monotone.f (interpS Θ) (Monotone.f (interpR ρ) k))
             (Monotone.f (interpS (ρ rs Θ)) k)
               (interp-rs-l ρ Θ k))
           (subst-eq-r (ρ rs Θ) e k)))
  sound {Γ} {τ} ._ .(ren (subst e Θ) ρ) (subst-rs-r ρ Θ e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e (ρ rs Θ))) k)
      (Monotone.f (interpE (subst e Θ)) (Monotone.f (interpR ρ) k))
      (Monotone.f (interpE (ren (subst e Θ) ρ)) k)
      (Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE (subst e (ρ rs Θ))) k)
        (Monotone.f (interpE e) (Monotone.f (interpS Θ) (Monotone.f (interpR ρ) k)))
        (Monotone.f (interpE (subst e Θ)) (Monotone.f (interpR ρ) k))
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e (ρ rs Θ))) k)
          (Monotone.f (interpE e) (Monotone.f (interpS (ρ rs Θ)) k))
          (Monotone.f (interpE e) (Monotone.f (interpS Θ) (Monotone.f (interpR ρ) k)))
          (subst-eq-l (ρ rs Θ) e k)
          (Monotone.is-monotone (interpE e)
            (Monotone.f (interpS (ρ rs Θ)) k)
            (Monotone.f (interpS Θ) (Monotone.f (interpR ρ) k))
              (interp-rs-r ρ Θ k)))
        (subst-eq-r Θ e (Monotone.f (interpR ρ) k)))
      (ren-eq-r ρ (subst e Θ) k)
  sound {Γ} {τ} .(subst (ren e ρ) Θ) ._ (subst-sr-l Θ ρ e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst (ren e ρ) Θ)) k)
      (Monotone.f (interpE (ren e ρ)) (Monotone.f (interpS Θ) k))
      (Monotone.f (interpE (subst e (Θ sr ρ))) k)
      (subst-eq-l Θ (ren e ρ) k)
      (Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE (ren e ρ)) (Monotone.f (interpS Θ) k))
        (Monotone.f (interpE e) (Monotone.f (interpS (Θ sr ρ)) k))
        (Monotone.f (interpE (subst e (Θ sr ρ))) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (ren e ρ)) (Monotone.f (interpS Θ) k))
          (Monotone.f (interpE e) (Monotone.f (interpR ρ) (Monotone.f (interpS Θ) k)))
          (Monotone.f (interpE e) (Monotone.f (interpS (Θ sr ρ)) k))
          (ren-eq-l ρ e (Monotone.f (interpS Θ) k))
          (Monotone.is-monotone (interpE e)
            (Monotone.f (interpR ρ) (Monotone.f (interpS Θ) k))
            (Monotone.f (interpS (Θ sr ρ)) k)
              (interp-sr-l Θ ρ k)))
        (subst-eq-r (Θ sr ρ) e k))
  sound {Γ} {τ} ._ .(subst (ren e ρ) Θ) (subst-sr-r Θ ρ e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e (Θ sr ρ))) k)
      (Monotone.f (interpE (ren e ρ)) (Monotone.f (interpS Θ) k))
      (Monotone.f (interpE (subst (ren e ρ) Θ)) k)
      (Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE (subst e (Θ sr ρ))) k)
        (Monotone.f (interpE e) (Monotone.f (interpS (Θ sr ρ)) k))
        (Monotone.f (interpE (ren e ρ)) (Monotone.f (interpS Θ) k))
        (subst-eq-l (Θ sr ρ) e k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE e) (Monotone.f (interpS (Θ sr ρ)) k))
          (Monotone.f (interpE e) (Monotone.f (interpR ρ) (Monotone.f (interpS Θ) k)))
          (Monotone.f (interpE (ren e ρ)) (Monotone.f (interpS Θ) k))
          (Monotone.is-monotone (interpE e)
            (Monotone.f (interpS (Θ sr ρ)) k)
            (Monotone.f (interpR ρ) (Monotone.f (interpS Θ) k))
              (interp-sr-r Θ ρ k))
          (ren-eq-r ρ e (Monotone.f (interpS Θ) k))))
      (subst-eq-r Θ (ren e ρ) k)
  sound {Γ} {τ} ._ .(subst (subst e Θ2) Θ1) (subst-ss-l Θ1 Θ2 e) k =
    Preorder-str.trans (snd [ τ ]t)
     (Monotone.f (interpE (subst e (Θ1 ss Θ2))) k)
     (Monotone.f (interpE e) (Monotone.f (interpS (Θ1 ss Θ2)) k))
     (Monotone.f (interpE (subst (subst e Θ2) Θ1)) k)
     (subst-eq-l (Θ1 ss Θ2) e k)
     (Preorder-str.trans (snd [ τ ]t)
       (Monotone.f (interpE e) (Monotone.f (interpS (Θ1 ss Θ2)) k))
       (Monotone.f (interpE (subst e Θ2)) (Monotone.f (interpS Θ1) k))
       (Monotone.f (interpE (subst (subst e Θ2) Θ1)) k)
       (Preorder-str.trans (snd [ τ ]t)
         (Monotone.f (interpE e) (Monotone.f (interpS (Θ1 ss Θ2)) k))
         (Monotone.f (interpE e) (Monotone.f (interpS Θ2) (Monotone.f (interpS Θ1) k)))
         (Monotone.f (interpE (subst e Θ2)) (Monotone.f (interpS Θ1) k))
         (Monotone.is-monotone (interpE e)
           (Monotone.f (interpS (Θ1 ss Θ2)) k)
           (Monotone.f (interpS Θ2) (Monotone.f (interpS Θ1) k))
             (interp-ss-l Θ1 Θ2 k))
         (subst-eq-r Θ2 e (Monotone.f (interpS Θ1) k)))
       (subst-eq-r Θ1 (subst e Θ2) k))
  sound {Γ} {τ} .(subst (subst e Θ2) Θ1) ._ (subst-ss-r Θ1 Θ2 e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst (subst e Θ2) Θ1)) k)
      (Monotone.f (interpE e) (Monotone.f (interpS (Θ1 ss Θ2)) k))
      (Monotone.f (interpE (subst e (Θ1 ss Θ2))) k)
      (Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE (subst (subst e Θ2) Θ1)) k)
        (Monotone.f (interpE (subst e Θ2)) (Monotone.f (interpS Θ1) k))
        (Monotone.f (interpE e) (Monotone.f (interpS (Θ1 ss Θ2)) k))
        (subst-eq-l Θ1 (subst e Θ2) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e Θ2)) (Monotone.f (interpS Θ1) k))
          (Monotone.f (interpE e) (Monotone.f (interpS Θ2) (Monotone.f (interpS Θ1) k)))
          (Monotone.f (interpE e) (Monotone.f (interpS (Θ1 ss Θ2)) k))
          (subst-eq-l Θ2 e (Monotone.f (interpS Θ1) k))
          (Monotone.is-monotone (interpE e)
            (Monotone.f (interpS Θ2) (Monotone.f (interpS Θ1) k))
            (Monotone.f (interpS (Θ1 ss Θ2)) k)
              (interp-ss-r Θ1 Θ2 k))))
      (subst-eq-r (Θ1 ss Θ2) e k)
  sound {Γ} {τ} ._ .(subst e (lem3' Θ v)) (subst-compose-l {.Γ} {Γ'} {τ'} Θ v e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst (subst e (s-extend Θ)) (q v))) k)
      (Monotone.f (interpE (subst e (s-extend Θ))) (Monotone.f (interpS (q v)) k))
      (Monotone.f (interpE (subst e (lem3' Θ v))) k)
      (subst-eq-l (q v) (subst e (s-extend Θ)) k)
      (Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE (subst e (s-extend Θ))) (Monotone.f (interpS (q v)) k))
        (Monotone.f (interpE e) (Monotone.f (interpS (lem3' Θ v)) k))
        (Monotone.f (interpE (subst e (lem3' Θ v))) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e (s-extend Θ))) (Monotone.f (interpS (q v)) k))
          (Monotone.f (interpE e) (Monotone.f (interpS {τ' :: Γ} {τ' :: Γ'} (s-extend {Γ} {Γ'} Θ)) (Monotone.f (interpS {Γ} {τ' :: Γ} (q v)) k)))
          (Monotone.f (interpE e) (Monotone.f (interpS (lem3' Θ v)) k))
          (subst-eq-l (s-extend Θ) e (Monotone.f (interpS (q v)) k))
          (Monotone.is-monotone (interpE e)
            (Monotone.f (interpS {τ' :: Γ} {τ' :: Γ'} (s-extend {Γ} {Γ'} Θ)) (Monotone.f (interpS {Γ} {τ' :: Γ} (q v)) k))
            (Monotone.f (interpS (lem3' Θ v)) k)
            (Preorder-str.trans (snd [ Γ' ]c)
              (fst (Monotone.f (interpS (s-extend Θ)) (Monotone.f (interpS (q v)) k)))
              (Monotone.f (interpS (λ x → subst (ren (Θ x) iS) (lem3' ids v))) k)
              (Monotone.f (interpS Θ) k)
              (fst (interp-ss-r (q v) (s-extend Θ) k))
              (interp-subst-comp-l Θ v k) ,
            Preorder-str.refl (snd [ τ' ]t) (Monotone.f (interpE v) k))))
        (subst-eq-r (lem3' Θ v) e k))
  sound {Γ} {τ} .(subst e (lem3' Θ v)) ._ (subst-compose-r {.Γ} {Γ'} {τ'} Θ v e) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e (lem3' Θ v))) k)
      (Monotone.f (interpE (subst e (s-extend Θ))) (Monotone.f (interpS (q v)) k))
      (Monotone.f (interpE (subst (subst e (s-extend Θ)) (q v))) k)
      (Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE (subst e (lem3' Θ v))) k)
        (Monotone.f (interpE e) (Monotone.f (interpS (lem3' Θ v)) k))
        (Monotone.f (interpE (subst e (s-extend Θ))) (Monotone.f (interpS (q v)) k))
        (subst-eq-l (lem3' Θ v) e k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE e) (Monotone.f (interpS (lem3' Θ v)) k))
          (Monotone.f (interpE e) (Monotone.f (interpS {τ' :: Γ} {τ' :: Γ'} (s-extend {Γ} {Γ'} Θ)) (Monotone.f (interpS {Γ} {τ' :: Γ} (q v)) k)))
          (Monotone.f (interpE (subst e (s-extend Θ))) (Monotone.f (interpS (q v)) k))
          (Monotone.is-monotone (interpE e)
            (Monotone.f (interpS (lem3' Θ v)) k)
            (Monotone.f (interpS {τ' :: Γ} {τ' :: Γ'} (s-extend {Γ} {Γ'} Θ)) (Monotone.f (interpS {Γ} {τ' :: Γ} (q v)) k))
              ((Preorder-str.trans (snd [ Γ' ]c)
                (Monotone.f (interpS Θ) k)
                (Monotone.f (interpS (λ x → subst (ren (Θ x) iS) (lem3' ids v))) k)
                (fst (Monotone.f (interpS (s-extend Θ)) (Monotone.f (interpS (q v)) k)))
                (interp-subst-comp-r Θ v k)
                (fst (interp-ss-l (q v) (s-extend Θ) k))) ,
              (Preorder-str.refl (snd [ τ' ]t) (Monotone.f (interpE v) k))))
          (subst-eq-r (s-extend Θ) e (Monotone.f (interpS (q v)) k))))
      (subst-eq-r (q v) (subst e (s-extend Θ)) k)
  sound {Γ} {τ} ._ .(subst e1 (lem3' (lem3' Θ v2) v1)) (subst-compose2-l {.Γ} {Γ'} {.τ} {τ'} {τ''} Θ e1 v1 v2) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst (subst e1 (s-extend (s-extend Θ))) (lem4 v1 v2))) k)
      (Monotone.f (interpE (subst e1 (s-extend (s-extend Θ)))) (Monotone.f (interpS (lem4 v1 v2)) k))
      (Monotone.f (interpE (subst e1 (lem4' Θ v1 v2))) k)
      (subst-eq-l (lem4 v1 v2) (subst e1 (s-extend (s-extend Θ))) k)
      (Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE (subst e1 (s-extend (s-extend Θ)))) (Monotone.f (interpS (lem4 v1 v2)) k))
        (Monotone.f (interpE e1) (Monotone.f (interpS (lem4' Θ v1 v2)) k))
        (Monotone.f (interpE (subst e1 (lem4' Θ v1 v2))) k)
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE (subst e1 (s-extend (s-extend Θ)))) (Monotone.f (interpS (lem4 v1 v2)) k))
          (Monotone.f (interpE e1) (Monotone.f (interpS (s-extend (s-extend Θ))) (Monotone.f (interpS (lem4 v1 v2)) k)))
          (Monotone.f (interpE e1) (Monotone.f (interpS (lem4' Θ v1 v2)) k))
          (subst-eq-l (s-extend (s-extend Θ)) e1 (Monotone.f (interpS (lem4 v1 v2)) k))
          (Monotone.is-monotone (interpE e1)
            (Monotone.f (interpS (s-extend (s-extend Θ))) (Monotone.f (interpS (lem4 v1 v2)) k))
            (Monotone.f (interpS (lem4' Θ v1 v2)) k)
            ((Preorder-str.trans (snd [ Γ' ]c)
              (Monotone.f (interpS (λ x → ren (ren (Θ x) iS) iS)) ((Monotone.f (interpS ids) k , Monotone.f (interpE v2) k) , Monotone.f (interpE v1) k))
              (Monotone.f (interpS (λ x → subst (ren (Θ x) iS) (lem3' ids v2))) k)
              (Monotone.f (interpS Θ) k)
              {!!}
              (interp-subst-comp-l Θ v2 k) ,
            Preorder-str.refl (snd [ τ'' ]t) (Monotone.f (interpE v2) k)) ,
            Preorder-str.refl (snd [ τ' ]t) (Monotone.f (interpE v1) k))))
        (subst-eq-r (lem4' Θ v1 v2) e1 k))
  sound .(subst e1 (lem3' (lem3' Θ v2) v1)) ._ (subst-compose2-r Θ e1 v1 v2) k = {!!}
  sound ._ .(subst e1 (lem3' (lem3' Θ (subst v2 Θ)) (subst v1 Θ))) (subst-compose3-l Θ e1 v1 v2) k = {!!}
  sound .(subst e1 (lem3' (lem3' Θ (subst v2 Θ)) (subst v1 Θ))) ._ (subst-compose3-r Θ e1 v1 v2) k = {!!}
  sound ._ .(subst e2 (lem3' (lem3' Θ r) v')) (subst-compose4-l Θ v' r e2) k = {!!}
  sound .(subst e2 (lem3' (lem3' Θ r) v')) ._ (subst-compose4-r Θ v' r e2) k = {!!}
  sound ._ .(subst e (lem3' (lem3' (lem3' Θ v3) v2) v1)) (subst-compose5-l Θ e v1 v2 v3) k = {!!}
  sound .(subst e (lem3' (lem3' (lem3' Θ v3) v2) v1)) ._ (subst-compose5-r Θ e v1 v2 v3) k = {!!}

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
  sound : ∀ {Γ τ} (e e' : Γ |- τ) → e ≤s e' → PREORDER≤ ([ Γ ]c ->p [ τ ]t) (interpE e) (interpE e')
  fix-x : ∀ {Γ τ} → (e : Γ |- nat) → (e₁ : Γ |- τ) → (e₂ : nat :: τ :: Γ |- τ) → (x y : fst [ Γ ]c) → (x₁ : Preorder-str.≤ (snd [ Γ ]c) x y)
        → Preorder-str.≤ (snd [ τ ]t)
          (natrec (Monotone.f (interpE e₁) x) (λ n x₂ → Monotone.f (interpE e₂) ((x , x₂) , n)) (Monotone.f (interpE e) x))
          (natrec (Monotone.f (interpE e₁) y) (λ n x₂ → Monotone.f (interpE e₂) ((y , x₂) , n)) (Monotone.f (interpE e) x))
  fix-branch : ∀ {Γ τ} → (e : Γ |- nat) → (e₁ : Γ |- τ) → (e₂ : nat :: τ :: Γ |- τ) → (x y : fst [ Γ ]c) → (x₁ : Preorder-str.≤ (snd [ Γ ]c) x y)
             → Preorder-str.≤ (snd [ τ ]t)
               (natrec (Monotone.f (interpE e₁) y) (λ n x₂ → Monotone.f (interpE e₂) ((y , x₂) , n)) (Monotone.f (interpE e) x))
               (natrec (Monotone.f (interpE e₁) y) (λ n x₂ → Monotone.f (interpE e₂) ((y , x₂) , n)) (Monotone.f (interpE e) y))
  interpE unit = monotone (λ x → <>) (λ x y x₁ → <>)
  interpE 0C = monotone (λ x → Z) (λ x y x₁ → <>)
  interpE 1C = monotone (λ x → S Z) (λ x y x₁ → <>)
  interpE (plusC e e₁) =
    monotone (λ x → Monotone.f (interpE e) x + Monotone.f (interpE e₁) x)
             (λ x y x₁ → plus-lem (Monotone.f (interpE e) x) (Monotone.f (interpE e₁) x) (Monotone.f (interpE e) y) (Monotone.f (interpE e₁) y)
               (Monotone.is-monotone (interpE e) x y x₁) {!!}) --(Monotone.is-monotone (interpE e) x y x₁) (Monotone.is-monotone (interpE e₁) x y x₁))
  interpE (var x) = lookup x
  interpE z = monotone (λ x → Z) (λ x y x₁ → <>)
  interpE (s e) = monotone (λ x → S (Monotone.f (interpE e) x)) (λ x y x₁ → Monotone.is-monotone (interpE e) x y x₁)
  interpE {Γ} {τ} (rec e e₁ e₂) =
    monotone (λ x → natrec (Monotone.f (interpE e₁) x) (λ n x₂ → Monotone.f (interpE e₂) ((x , x₂) , n)) (Monotone.f (interpE e) x))
             (λ x y x₁ →
               Preorder-str.trans (snd [ τ ]t)
                 (natrec (Monotone.f (interpE e₁) x) (λ n x₂ → Monotone.f (interpE e₂) ((x , x₂) , n)) (Monotone.f (interpE e) x))
                 (natrec (Monotone.f (interpE e₁) y) (λ n x₂ → Monotone.f (interpE e₂) ((y , x₂) , n)) (Monotone.f (interpE e) x))
                 (natrec (Monotone.f (interpE e₁) y) (λ n x₂ → Monotone.f (interpE e₂) ((y , x₂) , n)) (Monotone.f (interpE e) y))
                 (fix-x e e₁ e₂ x y x₁)
                 (fix-branch e e₁ e₂ x y x₁))
  interpE (lam e) = lam' (interpE e)
  interpE (app e e₁) = app' (interpE e) (interpE e₁)
  interpE rz = z'
  interpE (rsuc e) = suc' (interpE e)
-- comp' : MONOTONE PA PB → MONOTONE PB PC → MONOTONE PA PC
-- rec' is MONOTONE (PΓ ×p PN) PC
-- want (e0 : MONOTONE PΓ PC) → (e1 : MONOTONE (PΓ ×p (PN ×p PC)) PC)
-- have interpE e1 == PΓ PC
-- have interpE e2 == PΓ (PN -> PC -> PC)
-- turn PΓ (PN -> PC -> PC) into (PΓ ×p (PN ×p PC)) PC)
-- comp → PΓ (PΓ × PN) → (PΓ × PN) PC → PΓ PC
-- want (e2 : MONOTONE (PΓ ×p (PN ×p PC)) PC)
-- comp → PΓ 
-- have : .Γ |- (rnat ->c (.τ ->c .τ))
{-MONOTONE ((fst [ .Γ ]c , snd [ .Γ ]c) ×p (PN ×p (fst [ .τ ]t , snd [ .τ ]t)))
           (fst [ .τ ]t , snd [ .τ ]t)-}
--(app' (app' (interpE e₂) z') (interpE e₁)) is MONOTONE PΓ PC
  interpE (rrec e e₁ e₂ P) = comp (pair' id (interpE e)) (rec' (interpE e₁) {!!} (λ x → sound e₁ (app (app e₂ rz) e₁) P x))
--(comp {!!} (app' (app' (interpE e₂) z') (interpE e₁)))
  interpE (prod e e₁) = pair' (interpE e) (interpE e₁)
  interpE (l-proj e) = fst' (interpE e)
  interpE (r-proj e) = snd' (interpE e)
  interpE nil = nil'
  interpE (e ::c e₁) = cons' (interpE e) (interpE e₁)
  interpE (listrec e e₁ e₂) = comp (pair' id (interpE e)) (lrec' (interpE e₁) {!!})
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
  fix-x {Γ} {τ} e e₁ e₂ x y p with (Monotone.f (interpE e) x)
  fix-x e e₁ e₂ x y p | Z = Monotone.is-monotone (interpE e₁) x y p
  fix-x e e₁ e₂ x y p | S m = Monotone.is-monotone (interpE e₂)
    ((x , natrec (Monotone.f (interpE e₁) x) (λ n x₂ → Monotone.f (interpE e₂) ((x , x₂) , n)) m) , m)
    ((y , natrec (Monotone.f (interpE e₁) y) (λ n x₂ → Monotone.f (interpE e₂) ((y , x₂) , n)) m) , m)
      ((p , {!!}) , (♭nat-refl m))
  fix-branch {Γ} {τ} e e₁ e₂ x y p = {!!}

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

  ren-eq-l-lam : ∀ {Γ Γ' τ τ1} → (ρ : rctx Γ Γ') → (e : τ1 :: Γ' |- τ) → (k : fst [ Γ ]c) → (x : fst [ τ1 ]t)
               → Preorder-str.≤ (snd [ τ ]t)
                   (Monotone.f (interpE (ren e (r-extend ρ))) (k , x))
                   (Monotone.f (interpE e) (Monotone.f (interpR ρ) k , x))
  ren-eq-l-lam ρ e k x = {!!}

  mutual
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
    ren-eq-l ρ (rec e e₁ e₂) k = {!!}
    ren-eq-l {Γ} {τ = τ1 ->c τ2} ρ (lam e) k x =
      Preorder-str.trans (snd [ τ2 ]t)
        (Monotone.f (Monotone.f (interpE (ren (lam e) ρ)) k) x)
        (Monotone.f (interpE e) (Monotone.f (interpR (r-extend {_} {_} {τ1} ρ)) (k , x)))
        (Monotone.f (Monotone.f (interpE (lam e)) (Monotone.f (interpR ρ) k)) x)
          (ren-eq-l (r-extend ρ) e (k , x))
          (Preorder-str.trans (snd [ τ2 ]t)
            (Monotone.f (interpE e) (Monotone.f (interpR (r-extend {_} {_} {τ1} ρ)) (k , x)))
            (Monotone.f (interpE (ren e (r-extend ρ))) (k , x))
            (Monotone.f (Monotone.f (interpE (lam e)) (Monotone.f (interpR ρ) k)) x)
              (ren-eq-r (r-extend ρ) e (k , x))
              {!!})
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
    ren-eq-r : ∀ {Γ Γ' τ} → (ρ : rctx Γ Γ') → (e : Γ' |- τ) → (k : fst [ Γ ]c)
             → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)) (Monotone.f (interpE (ren e ρ)) k)
    ren-eq-r ρ e k = {!!}

  mutual
    subst-eq-l : ∀ {Γ Γ' τ} → (Θ : sctx Γ Γ') → (e : Γ' |- τ) → (k : fst [ Γ ]c)
             → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
    subst-eq-l Θ e k = {!!}
    subst-eq-r : ∀ {Γ Γ' τ} → (Θ : sctx Γ Γ') → (e : Γ' |- τ) → (k : fst [ Γ ]c)
             → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)) (Monotone.f (interpE (subst e Θ)) k)
    subst-eq-r Θ e k = {!!}

{-
  postulate
    ren-eq-lem' : ∀ {Γ Γ' τ1 τ2} → (ρ : rctx Γ Γ') → (e : τ1 :: Γ' |- τ2) → (k : fst [ Γ ]c)
                → ((λ p₁ → Monotone.f (interpE (ren e (r-extend ρ))) (k , p₁)) == (λ p₁ → Monotone.f (interpE e) (Monotone.f (interpR ρ) k , p₁))) 
                → monotone (λ p₁ → Monotone.f (interpE (ren e (r-extend ρ))) (k , p₁))
                  (λ a b c → Monotone.is-monotone (interpE (ren e (r-extend ρ))) (k , a) (k , b)
                    (Preorder-str.refl (snd [ Γ ]c) k , c)) ==
                  monotone (λ p₁ → Monotone.f (interpE e) (Monotone.f (interpR ρ) k , p₁))
                  (λ a b c → Monotone.is-monotone (interpE e) (Monotone.f (interpR ρ) k , a) (Monotone.f (interpR ρ) k , b)
                    (Preorder-str.refl (snd [ Γ' ]c) (Monotone.f (interpR ρ) k) , c))

  mutual
    ren-eq-abs : ∀ {Γ Γ' τ1 τ2} → (ρ : rctx Γ Γ') → (e : τ1 :: Γ' |- τ2) → (p₁ : fst [ τ1 ]t) → (k : fst [ Γ ]c)
                → _==_ {_} {_} (Monotone.f (interpR (r-extend {_} {_} {τ1} ρ)) (k , p₁)) (Monotone.f (interpR ρ) k , p₁)
    ren-eq-abs ρ e p₁ k = (Monotone.f (interpR (λ x → iS (ρ x))) (k , p₁) , p₁) =⟨ {!!} ⟩
                           ((Monotone.f (interpR ρ) k , p₁) ∎)

    ren-eq-lem : ∀ {Γ Γ' τ} → (ρ : rctx Γ Γ') → (e : Γ' |- τ) → (k : fst [ Γ ]c) → Monotone.f (interpE (ren e ρ)) k == Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
    ren-eq-lem ρ unit k = Refl
    ren-eq-lem ρ 0C k = Refl
    ren-eq-lem ρ 1C k = Refl
    ren-eq-lem ρ (plusC e e₁) k = ap2 _+_ (ren-eq-lem ρ e k) (ren-eq-lem ρ e₁ k)
    ren-eq-lem ρ (var i0) k = Refl
    ren-eq-lem ρ (var (iS x)) k = ren-eq-lem (throw-r ρ) (var x) k
    ren-eq-lem ρ z k = Refl
    ren-eq-lem ρ (s e) k = ap S (ren-eq-lem ρ e k)
    ren-eq-lem ρ (rec e e₁ e₂) k = ap3 natrec (ren-eq-lem ρ e₁ k) (λ= (λ n → λ= (λ x₂ → {!!} ∘ ren-eq-lem (r-extend (r-extend ρ)) e₂ ((k , x₂) , n)))) (ren-eq-lem ρ e k)
    ren-eq-lem {Γ} {Γ'} {τ1 ->c τ2} ρ (lam e) k = ren-eq-lem' ρ e k (λ= (λ p₁ → {!!} ∘ ren-eq-lem (r-extend ρ) e (k , p₁)))
    ren-eq-lem ρ (app e e₁) k = ap2 (λ x x₁ → Monotone.f x x₁) (ren-eq-lem ρ e k) (ren-eq-lem ρ e₁ k)
    ren-eq-lem ρ rz k = Refl
    ren-eq-lem ρ (rsuc e) k = ap S (ren-eq-lem ρ e k)
    ren-eq-lem ρ (rrec e e₁ e₂ P) k = ap3 natrec (ren-eq-lem ρ e₁ k) (λ= (λ n → λ= (λ x₂ → {!!}))) (ren-eq-lem ρ e k)
    ren-eq-lem ρ (prod e e₁) k = ap2 (λ x x₁ → x , x₁) (ren-eq-lem ρ e k) (ren-eq-lem ρ e₁ k)
    ren-eq-lem ρ (l-proj e) k = ap fst (ren-eq-lem ρ e k)
    ren-eq-lem ρ (r-proj e) k = ap snd (ren-eq-lem ρ e k)
    ren-eq-lem ρ nil k = Refl
    ren-eq-lem ρ (e ::c e₁) k = ap2 _::_ (ren-eq-lem ρ e k) (ren-eq-lem ρ e₁ k)
    ren-eq-lem ρ (listrec e e₁ e₂) k = ap3 lrec (ren-eq-lem ρ e k) (ren-eq-lem ρ e₁ k) (λ= (λ h → λ= (λ t → λ= (λ x₃ → {!!}))))
    ren-eq-lem ρ true k = Refl
    ren-eq-lem ρ false k = Refl
    ren-eq-lem ρ (max τ e1 e2) k = ap2 (Preorder-max-str.max [ τ ]tm) (ren-eq-lem ρ e1 k) (ren-eq-lem ρ e2 k)
-}
{-
  postulate
    subst-id-lem' : ∀ {Γ τ ρ} → (e : ρ :: Γ |- τ) → (k : fst [ Γ ]c)
                  → (λ p₁ → Monotone.f (interpE e) (k , p₁)) == (λ p₁ → Monotone.f (interpE (subst e (s-extend (λ {τ} x → var x)))) (k , p₁))
                  → monotone (λ p₁ → Monotone.f (interpE e) (k , p₁))
                    (λ a b c → Monotone.is-monotone (interpE e) (k , a) (k , b)
                      (Preorder-str.refl (snd [ Γ ]c) k , c)) ==
                    monotone (λ p₁ →  Monotone.f (interpE (subst e (s-extend (λ {τ} x → var x)))) (k , p₁))
                    (λ a b c → Monotone.is-monotone (interpE (subst e (s-extend (λ {τ} x → var x)))) (k , a) (k , b)
                      (Preorder-str.refl (snd [ Γ ]c) k , c))

  extend-id-thrice : ∀ {Γ τ1 τ2 τ3} → Id {_} {sctx (τ1 :: τ2 :: τ3 :: Γ) (τ1 :: τ2 :: τ3 :: Γ)} (ids {τ1 :: τ2 :: τ3 :: Γ}) (s-extend (s-extend (s-extend ids)))
  extend-id-thrice = ap s-extend extend-id-twice ∘ extend-id-once

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

    subst-id-lem : ∀ {Γ τ} → (e : Γ |- τ) → (k : fst [ Γ ]c) → (Monotone.f (interpE e) k) == (Monotone.f (interpE (subst e ids)) k)
    subst-id-lem unit k = Refl
    subst-id-lem 0C k = Refl
    subst-id-lem 1C k = Refl
    subst-id-lem (plusC e e₁) k = ap2 _+_ (subst-id-lem e k) (subst-id-lem e₁ k)
    subst-id-lem (var x) k = Refl
    subst-id-lem z k = Refl
    subst-id-lem (s e) k = ap S (subst-id-lem e k)
    subst-id-lem (rec e e₁ e₂) k = ap3 natrec (subst-id-lem e₁ k) (λ= (λ n → λ= (λ x₂ → subst-id-rec e₂ k n x₂))) (subst-id-lem e k)
    subst-id-lem {Γ} (lam e) k = subst-id-lem' e k (λ= (λ p₁ → subst-id-abs e k p₁))
    subst-id-lem (app e e₁) k = ap2 (λ x x₁ → Monotone.f x x₁) (subst-id-lem e k) (subst-id-lem e₁ k)
    subst-id-lem rz k = Refl
    subst-id-lem (rsuc e) k = ap S (subst-id-lem e k)
    subst-id-lem (rrec e e₁ e₂ P) k = ap3 natrec (subst-id-lem e₁ k) (λ= (λ n → λ= (λ x₂ → {!!}))) (subst-id-lem e k)
    subst-id-lem (prod e e₁) k = ap2 (λ x x₁ → x , x₁) (subst-id-lem e k) (subst-id-lem e₁ k)
    subst-id-lem (l-proj e) k = ap fst (subst-id-lem e k)
    subst-id-lem (r-proj e) k = ap snd (subst-id-lem e k)
    subst-id-lem nil k = Refl
    subst-id-lem (e ::c e₁) k = ap2 _::_ (subst-id-lem e k) (subst-id-lem e₁ k)
    subst-id-lem (listrec e e₁ e₂) k = ap3 lrec (subst-id-lem e k) (subst-id-lem e₁ k) (λ= (λ h → λ= (λ t → λ= (λ x₃ → subst-id-lrec e₂ k h t x₃))))
    subst-id-lem true k = Refl
    subst-id-lem false k = Refl
    subst-id-lem (max τ e e₁) k = ap2 (Preorder-max-str.max [ τ ]tm) (subst-id-lem e k) (subst-id-lem e₁ k)
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
      (natrec (Monotone.f (interpE e₁) k) (λ n x₂ → Monotone.f (interpE e₂) ((k , x₂) , n)) (Monotone.f (interpE e) k))
      {!!}
      (natrec (Monotone.f (interpE (subst e₁ ids)) k) (λ n x₂ → Monotone.f (interpE (subst e₂ (s-extend (s-extend ids)))) ((k , x₂) , n)) (Monotone.f (interpE (subst e ids)) k))
        {!s-id-l e₁ k!} {!!}
{-Preorder-str.≤ (snd [ τ ]t)
      (natrec (Monotone.f (interpE e₁) k)
       (λ n x₂ → Monotone.f (interpE e₂) ((k , x₂) , n))
       (Monotone.f (interpE e) k))
      (natrec (Monotone.f (interpE (subst e₁ (λ {τ₁} x → var x))) k)
       (λ n x₂ →
          Monotone.f
          (interpE (subst e₂ (s-extend (s-extend (λ {τ₁} x → var x)))))
          ((k , x₂) , n))
       (Monotone.f (interpE (subst e (λ {τ₁} x → var x))) k))-}
                                   {-Preorder-str.trans (snd [ τ ]t)
                                     (Monotone.f (interpE (rec e e₁ e₂)) k)
                                     (Monotone.f (interpE (rec e e₁ e₂)) (Monotone.f (interpS {Γ} {_} ids) k))
                                     (Monotone.f (interpE (subst (rec e e₁ e₂) ids)) k)
                                       (Monotone.is-monotone (interpE (rec e e₁ e₂)) k (Monotone.f (interpS {Γ} {_} ids) k) {!!})
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
  s-id-l {_} {τ} (max x e e₁) k = {!!}
  s-id-r : ∀ {Γ τ} → (e : Γ |- τ) → (k : fst [ Γ ]c) → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e ids)) k) (Monotone.f (interpE e) k)
  s-id-r = {!!}

  s-rr-l : ∀ {Γ Γ' Γ'' τ} → (e : Γ'' |- τ) (ρ1 : rctx Γ Γ') (ρ2 : rctx Γ' Γ'') → (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (ren (ren e ρ2) ρ1)) k) (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k)
  s-rr-l unit ρ1 ρ2 k = <>
  s-rr-l 0C ρ1 ρ2 k = <>
  s-rr-l 1C ρ1 ρ2 k = <>
  s-rr-l (plusC e e₁) ρ1 ρ2 k = {!!}
  s-rr-l {τ = τ} (var x) ρ1 ρ2 k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (lookup (ρ1 (ρ2 x))) k)
  s-rr-l z ρ1 ρ2 k = <>
  s-rr-l (s e) ρ1 ρ2 k = {!!}
  s-rr-l (rec e e₁ e₂) ρ1 ρ2 k = {!!}
  s-rr-l (lam e) ρ1 ρ2 k x = {!!}
  s-rr-l (app e e₁) ρ1 ρ2 k = {!!}
  s-rr-l rz ρ1 ρ2 k = <>
  s-rr-l (rsuc e) ρ1 ρ2 k = {!!}
  s-rr-l (rrec e e₁ e₂ P) ρ1 ρ2 k = {!!}
  s-rr-l (prod e e₁) ρ1 ρ2 k = {!!}
  s-rr-l (l-proj e) ρ1 ρ2 k = {!!}
  s-rr-l (r-proj e) ρ1 ρ2 k = {!!}
  s-rr-l nil ρ1 ρ2 k = <>
  s-rr-l (e ::c e₁) ρ1 ρ2 k = {!!}
  s-rr-l (listrec e e₁ e₂) ρ1 ρ2 k = {!!}
  s-rr-l true ρ1 ρ2 k = <>
  s-rr-l false ρ1 ρ2 k = <>
  s-rr-l (max x e e₁) ρ1 ρ2 k = {!!}
  s-rr-r : ∀ {Γ Γ' Γ'' τ} → (e : Γ'' |- τ) (ρ1 : rctx Γ Γ') (ρ2 : rctx Γ' Γ'') → (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k) (Monotone.f (interpE (ren (ren e ρ2) ρ1)) k)
  s-rr-r = {!!}

  s-rs-l : ∀ {Γ A B τ} (ρ : rctx Γ A) (Θ : sctx A B) (e : B |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (ren (subst e Θ) ρ)) k) (Monotone.f (interpE (subst e (ρ rs Θ))) k)
  s-rs-l = {!!}
  s-rs-r : ∀ {Γ A B τ} (ρ : rctx Γ A) (Θ : sctx A B) (e : B |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e (ρ rs Θ))) k) (Monotone.f (interpE (ren (subst e Θ) ρ)) k)
  s-rs-r = {!!}

  s-sr-l : ∀ {Γ Γ' Γ'' τ} (Θ : sctx Γ Γ') (ρ : rctx Γ' Γ'') (e : Γ'' |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst (ren e ρ) Θ)) k) (Monotone.f (interpE (subst e (Θ sr ρ))) k)
  s-sr-l = {!!}
  s-sr-r : ∀ {Γ Γ' Γ'' τ} (Θ : sctx Γ Γ') (ρ : rctx Γ' Γ'') (e : Γ'' |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e (Θ sr ρ))) k) (Monotone.f (interpE (subst (ren e ρ) Θ)) k)
  s-sr-r = {!!}

  s-ss-l : ∀ {Γ B C τ} (Θ1 : sctx Γ B) (Θ2 : sctx B C) (e : C |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e (Θ1 ss Θ2))) k) (Monotone.f (interpE (subst (subst e Θ2) Θ1)) k)
  s-ss-l = {!!}
  s-ss-r : ∀ {Γ B C τ} (Θ1 : sctx Γ B) (Θ2 : sctx B C) (e : C |- τ) (k : fst [ Γ ]c)
         → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst (subst e Θ2) Θ1)) k) (Monotone.f (interpE (subst e (Θ1 ss Θ2))) k)
  s-ss-r = {!!}

{-
  s-cong2 : ∀ {Γ Γ' τ} (Θ Θ' : sctx Γ Γ') (e : Γ' |- τ) (k : fst [ Γ ]c) (x : (τ₁ : CTp) (x₁ : τ₁ ∈ Γ') → Θ x₁ ≤s Θ' x₁)
          → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE (subst e Θ')) k)
  s-cong2 Θ Θ' e k x = ?
-}

{- Preorder-str.≤ (snd [ τ ]t)
      (Monotone.f (interpE (ren e1 (λ {.τ} → ρ))) k)
      (Monotone.f (interpE e1) (Monotone.f (interpR (λ {.τ} → ρ)) k))-}
--  sound : ∀ {Γ τ} (e e' : Γ |- τ) → e ≤s e' → PREORDER≤ ([ Γ ]c ->p [ τ ]t) (interpE e) (interpE e')
  sound {_} {τ} e .e refl-s k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {Γ} {τ} e e' (trans-s {.Γ} {.τ} {.e} {e''} {.e'} d d₁) k =
        Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE e) k) (Monotone.f (interpE e'') k) (Monotone.f (interpE e') k)
        (sound e e'' d k) (sound e'' e' d₁ k)
  sound {_} {τ} e .e (cong-refl Refl) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound .(plusC 0C e') e' +-unit-l k = Preorder-str.refl (snd [ rnat ]t) (Monotone.f (interpE e') k)
  sound e .(plusC 0C e) +-unit-l' k = Preorder-str.refl (snd [ rnat ]t) (Monotone.f (interpE e) k)
  sound {_} {.C} .(plusC e' 0C) e' +-unit-r k = +-unit (Monotone.f (interpE e') k)
  sound e .(plusC e 0C) +-unit-r' k = plus-lem' (Monotone.f (interpE e) k) (Monotone.f (interpE e) k) Z (nat-refl (Monotone.f (interpE e) k))
  sound {Γ} {.C} ._ ._ (+-assoc {.Γ} {e1} {e2} {e3}) k = plus-assoc (Monotone.f (interpE e1) k) (Monotone.f (interpE e2) k) (Monotone.f (interpE e3) k)
  sound {Γ} {.C} ._ ._ (+-assoc' {.Γ} {e1} {e2} {e3}) k = plus-assoc' (Monotone.f (interpE e1) k) (Monotone.f (interpE e2) k) (Monotone.f (interpE e3) k)
  sound {Γ} {.C} ._ ._ (refl-+ {.Γ} {e0} {e1}) k = +-comm (Monotone.f (interpE e0) k) (Monotone.f (interpE e1) k)
  sound {Γ} {C} ._ ._ (cong-+ {.Γ} {e0} {e1} {e0'} {e1'} d d₁) k = --also called plus-s
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
  sound {Γ} {τ} ._ ._ (subst-cong {.Γ} {Γ'} {.τ} {e1} {e2} {Θ} d) k = {!!}
  sound {Γ} {τ} ._ ._ (subst-cong2 {.Γ} {Γ'} {.τ} {Θ} {Θ'} {e} x) k = {!!}
  sound {Γ} {τ} ._ ._ (cong-rec {.Γ} {.τ} {e} {e'} {e0} {e1} d) k = {!!}
  sound ._ ._ (cong-listrec d) k = {!!}
  sound {Γ} {τ} ._ ._ (lam-s {.Γ} {τ'} {.τ} {e} {e2}) k = {!!}
  sound {Γ} {τ} e ._ (l-proj-s {.Γ}) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {Γ} {τ} e ._ (r-proj-s {.Γ}) k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound {_} {τ} e ._ rec-steps-z k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound ._ ._ rec-steps-s k = {!!}
  sound {Γ} {τ} e ._ listrec-steps-nil k = Preorder-str.refl (snd [ τ ]t) (Monotone.f (interpE e) k)
  sound ._ ._ listrec-steps-cons k = {!!}
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

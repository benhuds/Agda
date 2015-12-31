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

  el : PREORDER → Set
  el = fst

  PREORDER≤ : (PA : PREORDER) → el PA → el PA → Set
  PREORDER≤ PA = Preorder-str.≤ (snd PA)

  lookup : ∀{Γ τ} → τ ∈ Γ → el ([ Γ ]c ->p [ τ ]t)
  lookup (i0 {Γ} {τ}) = snd' id
  lookup (iS {Γ} {τ} {τ1} x) = comp (fst' id) (lookup x)

  nat-lemma3 : ∀ (x : Nat) → ≤nat x (S x)
  nat-lemma3 Z = <>
  nat-lemma3 (S x) = nat-lemma3 x

  plus-lem' : ∀ (a b c : Nat) → ≤nat a b → ≤nat a (b + c)
  plus-lem' Z Z Z <> = <>
  plus-lem' Z Z (S c) <> = <>
  plus-lem' Z (S b) c x = <>
  plus-lem' (S a) Z c ()
  plus-lem' (S a) (S b) c x = plus-lem' a b c x

  plus-rh-S : (n m : Nat) → ≤nat (S (n + m)) (n + S m)
  plus-rh-S Z m = nat-refl m
  plus-rh-S (S n) m = plus-rh-S n m

  +-unit : ∀ (a : Nat) → ≤nat (a + 0) a
  +-unit Z = <>
  +-unit (S a) = +-unit a

  +-comm : ∀ (a b : Nat) → ≤nat (a + b) (b + a)
  +-comm Z b = plus-lem' b b Z (nat-refl b)
  +-comm (S a) b = nat-trans (S (a + b)) (S (b + a)) (b + S a) (+-comm a b) (plus-rh-S b a)

  plus-assoc : ∀ (a b c : Nat) → ≤nat (a + (b + c)) ((a + b) + c)
  plus-assoc Z b c = nat-refl (b + c)
  plus-assoc (S a) b c = plus-assoc a b c

  plus-assoc' : ∀ (a b c : Nat) → ≤nat ((a + b) + c) (a + (b + c))
  plus-assoc' Z b c = nat-refl (b + c)
  plus-assoc' (S a) b c = plus-assoc' a b c

  mutual
    plus-lem'' : ∀ (a b : Nat) → ≤nat a (b + a)
    plus-lem'' a Z = nat-refl a
    plus-lem'' Z (S b) = <>
    plus-lem'' (S a) (S b) = nat-trans a (b + a) (b + S a) (plus-lem'' a b) (plus-lem b a b (S a) (nat-refl b) (nat-lemma3 a))

    plus-lem : ∀ (a b c d : Nat) → ≤nat a c → ≤nat b d → ≤nat (a + b) (c + d)
    plus-lem Z b Z d p q = q
    plus-lem Z Z (S c) Z p q = <>
    plus-lem Z (S b) (S c) Z p ()
    plus-lem Z Z (S c) (S d) p q = <>
    plus-lem Z (S b) (S c) (S d) p q = nat-trans b d (c + S d) q (nat-trans d (S d) (c + S d) (nat-lemma3 d) (plus-lem'' (S d) c))
    plus-lem (S a) b Z d () q
    plus-lem (S a) b (S c) d p q = plus-lem a b c d p q

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
               (Monotone.is-monotone (interpE e) x y x₁) (Monotone.is-monotone (interpE e₁) x y x₁))
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
  interpE (rrec e e₁ e₂ P) = comp (pair' id (interpE e)) (rec' (interpE e₁) (comp {!!} {!!}) (λ x → {!!}))
  interpE (prod e e₁) = pair' (interpE e) (interpE e₁)
  interpE (l-proj e) = fst' (interpE e)
  interpE (r-proj e) = snd' (interpE e)
  interpE nil = monotone (λ x → []) (λ x y x₁ → <>)
  interpE (e ::c e₁) =
    monotone (λ x → Monotone.f (interpE e) x :: Monotone.f (interpE e₁) x)
             (λ x y x₁ → (Monotone.is-monotone (interpE e) x y x₁) , Monotone.is-monotone (interpE e₁) x y x₁)
  interpE (listrec e e₁ e₂) =
    monotone (λ x → lrec (Monotone.f (interpE e) x) (Monotone.f (interpE e₁) x) (λ h t x₃ → Monotone.f (interpE e₂) (((x , x₃) , t) , h)))
             (λ x y x₁ → {!!})
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
{-
  postulate
    ren-eq-lem' : ∀ {Γ Γ' τ1 τ2} → (ρ : rctx Γ Γ') → (e : τ1 :: Γ' |- τ2) → (k : fst [ Γ ]c) → ((λ p₁ → Monotone.f (interpE (ren e (r-extend ρ))) (k , p₁)) == (λ p₁ → Monotone.f (interpE e) (Monotone.f (interpR ρ) k , p₁))) 
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

  subst-eq-lem : ∀ {Γ Γ' τ} → (Θ : sctx Γ Γ') → (e : Γ' |- τ) → (k : fst [ Γ ]c) → Monotone.f (interpE (subst e Θ)) k == Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  subst-eq-lem Θ unit k = Refl
  subst-eq-lem Θ 0C k = Refl
  subst-eq-lem Θ 1C k = Refl
  subst-eq-lem Θ (plusC e e₁) k = ap2 _+_ (subst-eq-lem Θ e k) (subst-eq-lem Θ e₁ k)
  subst-eq-lem Θ (var i0) k = Refl
  subst-eq-lem Θ (var (iS x)) k = subst-eq-lem (throw-s Θ) (var x) k
  subst-eq-lem Θ z k = Refl
  subst-eq-lem Θ (s e) k = ap S (subst-eq-lem Θ e k)
  subst-eq-lem Θ (rec e e₁ e₂) k = ap3 natrec (subst-eq-lem Θ e₁ k) (λ= (λ n → λ= (λ x₂ → {!!}))) (subst-eq-lem Θ e k)
  subst-eq-lem Θ (lam e) k = {!!}
  subst-eq-lem Θ (app e e₁) k = ap2 (λ x x₁ → Monotone.f x x₁) (subst-eq-lem Θ e k) (subst-eq-lem Θ e₁ k)
  subst-eq-lem Θ rz k = Refl
  subst-eq-lem Θ (rsuc e) k = ap S (subst-eq-lem Θ e k)
  subst-eq-lem Θ (rrec e e₁ e₂ P) k = ap3 natrec (subst-eq-lem Θ e₁ k) (λ= (λ n → λ= (λ x₂ → {!!}))) (subst-eq-lem Θ e k)
  subst-eq-lem Θ (prod e e₁) k = ap2 (λ x x₁ → x , x₁) (subst-eq-lem Θ e k) (subst-eq-lem Θ e₁ k)
  subst-eq-lem Θ (l-proj e) k = ap fst (subst-eq-lem Θ e k)
  subst-eq-lem Θ (r-proj e) k = ap snd (subst-eq-lem Θ e k)
  subst-eq-lem Θ nil k = Refl
  subst-eq-lem Θ (e ::c e₁) k = ap2 _::_ (subst-eq-lem Θ e k) (subst-eq-lem Θ e₁ k)
  subst-eq-lem Θ (listrec e e₁ e₂) k = ap3 lrec (subst-eq-lem Θ e k) (subst-eq-lem Θ e₁ k) (λ= (λ h → λ= (λ t → λ= (λ x₃ → {!!}))))
  subst-eq-lem Θ true k = Refl
  subst-eq-lem Θ false k = Refl
  subst-eq-lem Θ (max τ e1 e2) k = ap2 (Preorder-max-str.max [ τ ]tm) (subst-eq-lem Θ e1 k) (subst-eq-lem Θ e2 k)

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

  extend-ren-comp-twice : ∀ {Γ Γ' Γ'' τ1 τ2} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'')
                        → Id {_} {rctx (τ1 :: τ2 :: Γ) (τ1 :: τ2 :: Γ'')} ((r-extend (r-extend ρ1)) ∙rr (r-extend (r-extend ρ2))) (r-extend (r-extend (ρ1 ∙rr ρ2)))
  extend-ren-comp-twice ρ1 ρ2 = ap r-extend (extend-ren-comp ρ1 ρ2) ∘ extend-ren-comp (r-extend ρ1) (r-extend ρ2)

  extend-ren-comp-thrice : ∀ {Γ Γ' Γ'' τ1 τ2 τ3} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'')
                        → Id {_} {rctx (τ1 :: τ2 :: τ3 :: Γ) (τ1 :: τ2 :: τ3 :: Γ'')}
                          ((r-extend (r-extend (r-extend ρ1))) ∙rr (r-extend (r-extend (r-extend ρ2)))) (r-extend (r-extend (r-extend (ρ1 ∙rr ρ2))))
  extend-ren-comp-thrice ρ1 ρ2 = ap r-extend (extend-ren-comp-twice ρ1 ρ2) ∘ extend-ren-comp (r-extend (r-extend ρ1)) (r-extend (r-extend ρ2))

  postulate
    ren-comp-lem' : ∀ {Γ Γ' Γ'' τ ρ} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'') → (e : ρ :: Γ'' |- τ) → (k : fst [ Γ ]c)
                  → (λ p₁ → Monotone.f (interpE (ren (ren e (r-extend ρ2)) (r-extend ρ1))) (k , p₁)) ==
                    (λ p₁ → Monotone.f (interpE (ren e (r-extend (λ x → ρ1 (ρ2 x))))) (k , p₁))
                  → monotone (λ p₁ → Monotone.f (interpE (ren (ren e (r-extend ρ2)) (r-extend ρ1))) (k , p₁))
                    (λ a b c → Monotone.is-monotone (interpE (ren (ren e (r-extend ρ2)) (r-extend ρ1))) (k , a) (k , b)
                      (Preorder-str.refl (snd [ Γ ]c) k , c)) ==
                    monotone (λ p₁ → Monotone.f (interpE (ren e (r-extend (λ x → ρ1 (ρ2 x))))) (k , p₁))
                    (λ a b c → Monotone.is-monotone (interpE (ren e (r-extend (λ x → ρ1 (ρ2 x))))) (k , a) (k , b)
                      (Preorder-str.refl (snd [ Γ ]c) k , c))

  mutual
    ren-comp-abs : ∀ {Γ Γ' Γ'' τ ρ} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'') → (e : ρ :: Γ'' |- τ) → (k : fst [ Γ ]c) → (p₁ : fst [ ρ ]t)
                 → Monotone.f (interpE (ren (ren e (r-extend ρ2)) (r-extend ρ1))) (k , p₁) ==
                   Monotone.f (interpE (ren e (r-extend (λ x → ρ1 (ρ2 x))))) (k , p₁)
    ren-comp-abs ρ1 ρ2 e k p₁ = Monotone.f (interpE (ren (ren e (r-extend ρ2)) (r-extend ρ1))) (k , p₁) =⟨ ren-comp-lem (r-extend ρ1) (r-extend ρ2) e (k , p₁) ⟩
                                Monotone.f (interpE (ren e (r-extend ρ1 ∙rr r-extend ρ2))) (k , p₁) =⟨ ap2 Monotone.f (ap interpE (ap (ren e) (extend-ren-comp ρ1 ρ2))) Refl ⟩
                                (Monotone.f (interpE (ren e (r-extend (λ x → ρ1 (ρ2 x))))) (k , p₁) ∎)

    ren-comp-rec : ∀ {Γ Γ' Γ'' τ} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'') → (e : nat :: τ :: Γ'' |- τ) → (k : fst [ Γ ]c) → (n : Nat) → (x₂ : fst [ τ ]t)
                 → Monotone.f (interpE (ren (ren e (r-extend (r-extend ρ2))) (r-extend (r-extend ρ1)))) ((k , x₂) , n) ==
                   Monotone.f (interpE (ren e (r-extend (r-extend (ρ1 ∙rr ρ2))))) ((k , x₂) , n)
    ren-comp-rec ρ1 ρ2 e k n x₂ = Monotone.f (interpE (ren (ren e (r-extend (r-extend ρ2))) (r-extend (r-extend ρ1)))) ((k , x₂) , n)
                                    =⟨ ren-comp-lem (r-extend (r-extend ρ1)) (r-extend (r-extend ρ2)) e ((k , x₂) , n) ⟩
                                  Monotone.f (interpE (ren e (r-extend (r-extend ρ1) ∙rr r-extend (r-extend ρ2)))) ((k , x₂) , n)
                                    =⟨ ap2 Monotone.f (ap interpE (ap (ren e) (extend-ren-comp-twice ρ1 ρ2))) Refl ⟩
                                  (Monotone.f (interpE (ren e (r-extend (r-extend (ρ1 ∙rr ρ2))))) ((k , x₂) , n) ∎)

    ren-comp-lrec : ∀ {Γ Γ' Γ'' τ τ1} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'') → (e : τ1 :: list τ1 :: τ :: Γ'' |- τ) → (k : fst [ Γ ]c)
                 → (h : fst [ τ1 ]t) → (t : List (fst [ τ1 ]t)) → (x₃ : fst [ τ ]t)
                 →  Monotone.f (interpE (ren (ren e (r-extend (r-extend (r-extend ρ2)))) (r-extend (r-extend (r-extend ρ1))))) (((k , x₃) , t) , h)  ==
                    Monotone.f (interpE (ren e (r-extend (r-extend (r-extend (ρ1 ∙rr ρ2)))))) (((k , x₃) , t) , h)
    ren-comp-lrec ρ1 ρ2 e k h t x₃ = Monotone.f (interpE (ren (ren e (r-extend (r-extend (r-extend ρ2)))) (r-extend (r-extend (r-extend ρ1))))) (((k , x₃) , t) , h)
                                       =⟨ ren-comp-lem (r-extend (r-extend (r-extend ρ1))) (r-extend (r-extend (r-extend ρ2))) e (((k , x₃) , t) , h) ⟩
                                     Monotone.f (interpE (ren e (r-extend (r-extend (r-extend ρ1)) ∙rr  r-extend (r-extend (r-extend ρ2))))) (((k , x₃) , t) , h)
                                       =⟨ ap2 Monotone.f (ap interpE (ap (ren e) (extend-ren-comp-thrice ρ1 ρ2))) Refl ⟩
                                     (Monotone.f (interpE (ren e (r-extend (r-extend (r-extend (ρ1 ∙rr ρ2)))))) (((k , x₃) , t) , h) ∎)

    ren-comp-lem : ∀ {Γ Γ' Γ'' τ} → (ρ1 : rctx Γ Γ') → (ρ2 : rctx Γ' Γ'') → (e : Γ'' |- τ) → (k : fst [ Γ ]c)
                 → (Monotone.f (interpE (ren (ren e ρ2) ρ1)) k) == (Monotone.f (interpE (ren e (ρ1 ∙rr ρ2))) k)
    ren-comp-lem ρ1 ρ2 unit k = Refl
    ren-comp-lem ρ1 ρ2 0C k = Refl
    ren-comp-lem ρ1 ρ2 1C k = Refl
    ren-comp-lem ρ1 ρ2 (plusC e e₁) k = ap2 _+_ (ren-comp-lem ρ1 ρ2 e k) (ren-comp-lem ρ1 ρ2 e₁ k)
    ren-comp-lem ρ1 ρ2 (var x) k = Refl
    ren-comp-lem ρ1 ρ2 z k = Refl
    ren-comp-lem ρ1 ρ2 (s e) k = ap S (ren-comp-lem ρ1 ρ2 e k)
    ren-comp-lem ρ1 ρ2 (rec e e₁ e₂) k = ap3 natrec (ren-comp-lem ρ1 ρ2 e₁ k) (λ= (λ n → λ= (λ x₂ → ren-comp-rec ρ1 ρ2 e₂ k n x₂))) (ren-comp-lem ρ1 ρ2 e k)
    ren-comp-lem ρ1 ρ2 (lam e) k = ren-comp-lem' ρ1 ρ2 e k (λ= (λ p₁ → ren-comp-abs ρ1 ρ2 e k p₁))
    ren-comp-lem ρ1 ρ2 (app e e₁) k = ap2 (λ x x₁ → Monotone.f x x₁) (ren-comp-lem ρ1 ρ2 e k) (ren-comp-lem ρ1 ρ2 e₁ k)
    ren-comp-lem ρ1 ρ2 rz k = Refl
    ren-comp-lem ρ1 ρ2 (rsuc e) k = ap S (ren-comp-lem ρ1 ρ2 e k)
    ren-comp-lem ρ1 ρ2 (rrec e e₁ e₂ P) k = ap3 natrec (ren-comp-lem ρ1 ρ2 e₁ k) (λ= (λ n → λ= (λ x₂ → {!!}))) (ren-comp-lem ρ1 ρ2 e k)
    ren-comp-lem ρ1 ρ2 (prod e e₁) k = ap2 (λ x x₁ → x , x₁) (ren-comp-lem ρ1 ρ2 e k) (ren-comp-lem ρ1 ρ2 e₁ k)
    ren-comp-lem ρ1 ρ2 (l-proj e) k = ap fst (ren-comp-lem ρ1 ρ2 e k)
    ren-comp-lem ρ1 ρ2 (r-proj e) k = ap snd (ren-comp-lem ρ1 ρ2 e k)
    ren-comp-lem ρ1 ρ2 nil k = Refl
    ren-comp-lem ρ1 ρ2 (e ::c e₁) k = ap2 _::_ (ren-comp-lem ρ1 ρ2 e k) (ren-comp-lem ρ1 ρ2 e₁ k)
    ren-comp-lem ρ1 ρ2 (listrec e e₁ e₂) k = ap3 lrec (ren-comp-lem ρ1 ρ2 e k) (ren-comp-lem ρ1 ρ2 e₁ k) (λ= (λ h → λ= (λ t → λ= (λ x₃ → ren-comp-lrec ρ1 ρ2 e₂ k h t x₃))))
    ren-comp-lem ρ1 ρ2 true k = Refl
    ren-comp-lem ρ1 ρ2 false k = Refl
    ren-comp-lem ρ1 ρ2 (max x e e₁) k = ap2 (Preorder-max-str.max [ x ]tm) (ren-comp-lem ρ1 ρ2 e k) (ren-comp-lem ρ1 ρ2 e₁ k)

  extend-rs-once-lemma : ∀ {A B C τ τ'} → (x : τ ∈ τ' :: B) (ρ : rctx C A) (Θ : sctx A B)
                       → _==_ {_} {τ' :: C |- τ} (_rs_ {τ' :: C} {τ' :: A} {τ' :: B} (r-extend {C} {A} {τ'} ρ)
                         (s-extend {A} {B} {τ'} Θ) {τ} x) (s-extend {C} {B} {τ'} (_rs_ {C} {A} {B} ρ Θ) {τ} x)
  extend-rs-once-lemma i0 ρ Θ = Refl
  extend-rs-once-lemma (iS x) ρ Θ = {!!}

  extend-rs-once : ∀ {A B C τ} → (ρ : rctx C A) (Θ : sctx A B)
                 → Id {_} {sctx (τ :: C) (τ :: B)} (r-extend ρ rs s-extend Θ) (s-extend (ρ rs Θ))
  extend-rs-once ρ Θ = λ=i (λ τ → λ= (λ x → extend-rs-once-lemma x ρ Θ))

  extend-rs-twice : ∀ {A B C τ τ'} → (ρ : rctx C A) (Θ : sctx A B)
                  → Id {_} {sctx (τ :: τ' :: C) (τ :: τ' :: B)} ((r-extend (r-extend ρ)) rs (s-extend (s-extend Θ))) ((s-extend (s-extend (ρ rs Θ))))
  extend-rs-twice ρ Θ = ap s-extend (extend-rs-once ρ Θ) ∘ extend-rs-once (r-extend ρ) (s-extend Θ)

  extend-rs-thrice : ∀ {A B C τ τ' τ''} → (ρ : rctx C A) (Θ : sctx A B)
                  → Id {_} {sctx (τ :: τ' :: τ'' :: C) (τ :: τ' :: τ'' :: B)}
                    ((r-extend (r-extend (r-extend ρ))) rs (s-extend (s-extend (s-extend Θ)))) ((s-extend (s-extend (s-extend (ρ rs Θ)))))
  extend-rs-thrice ρ Θ = ap s-extend (extend-rs-twice ρ Θ) ∘ extend-rs-once (r-extend (r-extend ρ)) (s-extend (s-extend Θ))

  postulate
    rs-lem' : ∀ {Γ Γ' Γ'' τ τ'} → (Θ : sctx Γ Γ') → (ρ : rctx Γ'' Γ) → (e : τ' :: Γ' |- τ) → (k : fst [ Γ'' ]c)
            → (λ p₁ → Monotone.f (interpE (ren (subst e (s-extend Θ)) (r-extend ρ))) (k , p₁)) ==
              (λ p₁ → Monotone.f (interpE (subst e (s-extend (λ {τ} x → ren (Θ x) ρ)))) (k , p₁))
            → monotone (λ p₁ → Monotone.f (interpE (ren (subst e (s-extend Θ)) (r-extend ρ))) (k , p₁))
              (λ a b c → Monotone.is-monotone (interpE (ren (subst e (s-extend Θ)) (r-extend ρ))) (k , a) (k , b)
                (Preorder-str.refl (snd [ Γ'' ]c) k , c)) ==
              monotone (λ p₁ → Monotone.f (interpE (subst e (s-extend (λ {τ} x → ren (Θ x) ρ)))) (k , p₁))
              (λ a b c → Monotone.is-monotone (interpE (subst e (s-extend (λ {τ} x → ren (Θ x) ρ)))) (k , a) (k , b)
                (Preorder-str.refl (snd [ Γ'' ]c) k , c))

  mutual
    rs-lem-abs : ∀ {Γ Γ' Γ'' τ τ'} → (Θ : sctx Γ Γ') → (ρ : rctx Γ'' Γ) → (e : τ' :: Γ' |- τ) → (k : fst [ Γ'' ]c) → (p₁ : fst [ τ' ]t)
               → Monotone.f (interpE (ren (subst e (s-extend Θ)) (r-extend ρ))) (k , p₁) ==
                 Monotone.f (interpE (subst e (s-extend (λ x → ren (Θ x) ρ)))) (k , p₁)
    rs-lem-abs Θ ρ e k p₁ = Monotone.f (interpE (ren (subst e (s-extend Θ)) (r-extend ρ))) (k , p₁) =⟨ rs-lem (s-extend Θ) (r-extend ρ) e (k , p₁) ⟩
                            Monotone.f (interpE (subst e (r-extend ρ rs s-extend Θ))) (k , p₁) =⟨ ap2 Monotone.f (ap interpE (ap (subst e) (extend-rs-once ρ Θ))) Refl ⟩
                            (Monotone.f (interpE (subst e (s-extend (λ x → ren (Θ x) ρ)))) (k , p₁) ∎)

    rs-lem-rec : ∀ {Γ Γ' Γ'' τ} → (Θ : sctx Γ Γ') → (ρ : rctx Γ'' Γ) → (e₂ : nat :: τ :: Γ' |- τ) → (k : fst [ Γ'' ]c) → (n : Nat) → (x₂ : fst [ τ ]t)
               → Monotone.f (interpE (ren (subst e₂ (s-extend (s-extend Θ))) (r-extend (r-extend ρ)))) ((k , x₂) , n) ==
                 Monotone.f (interpE (subst e₂ (s-extend (s-extend (ρ rs Θ))))) ((k , x₂) , n)
    rs-lem-rec Θ ρ e₂ k n x₂ = Monotone.f (interpE (ren (subst e₂ (s-extend (s-extend Θ))) (r-extend (r-extend ρ)))) ((k , x₂) , n)
                                 =⟨ rs-lem (s-extend (s-extend Θ)) (r-extend (r-extend ρ)) e₂ ((k , x₂) , n) ⟩
                               Monotone.f (interpE (subst e₂ ((r-extend (r-extend ρ)) rs (s-extend (s-extend Θ))))) ((k , x₂) , n)
                                 =⟨ ap2 Monotone.f (ap interpE (ap (subst e₂) (extend-rs-twice ρ Θ))) Refl ⟩
                               (Monotone.f (interpE (subst e₂ (s-extend (s-extend (ρ rs Θ))))) ((k , x₂) , n) ∎)

    rs-lem-lrec : ∀ {Γ Γ' Γ'' τ τ1} → (Θ : sctx Γ Γ') → (ρ : rctx Γ'' Γ) → (e₂ : τ1 :: list τ1 :: τ :: Γ' |- τ) → (k : fst [ Γ'' ]c)
                → (h : fst [ τ1 ]t) → (t : List (fst [ τ1 ]t)) → (x₃ : fst [ τ ]t)
                → Monotone.f (interpE (ren (subst e₂ (s-extend (s-extend (s-extend Θ)))) (r-extend (r-extend (r-extend ρ))))) (((k , x₃) , t) , h) ==
                  Monotone.f (interpE (subst e₂ (s-extend (s-extend (s-extend (ρ rs Θ)))))) (((k , x₃) , t) , h)
    rs-lem-lrec Θ ρ e₂ k h t x₃ = Monotone.f (interpE (ren (subst e₂ (s-extend (s-extend (s-extend Θ)))) (r-extend (r-extend (r-extend ρ))))) (((k , x₃) , t) , h)
                                    =⟨ rs-lem (s-extend (s-extend (s-extend Θ))) (r-extend (r-extend (r-extend ρ))) e₂ (((k , x₃) , t) , h) ⟩
                                  Monotone.f (interpE (subst e₂ (r-extend (r-extend (r-extend ρ)) rs s-extend (s-extend (s-extend Θ))))) (((k , x₃) , t) , h)
                                    =⟨ ap2 Monotone.f (ap interpE (ap (subst e₂) (extend-rs-thrice ρ Θ))) Refl ⟩
                                  (Monotone.f (interpE (subst e₂ (s-extend (s-extend (s-extend (ρ rs Θ)))))) (((k , x₃) , t) , h) ∎)

    rs-lem : ∀ {Γ Γ' Γ'' τ} → (Θ : sctx Γ Γ') → (ρ : rctx Γ'' Γ) → (e : Γ' |- τ) → (k : fst [ Γ'' ]c)
           → (Monotone.f (interpE (ren (subst e Θ) ρ)) k) == (Monotone.f (interpE (subst e (ρ rs Θ))) k)
    rs-lem Θ ρ unit k = Refl
    rs-lem Θ ρ 0C k = Refl
    rs-lem Θ ρ 1C k = Refl
    rs-lem Θ ρ (plusC e e₁) k = ap2 _+_ (rs-lem Θ ρ e k) (rs-lem Θ ρ e₁ k)
    rs-lem Θ ρ (var x) k = Refl
    rs-lem Θ ρ z k = Refl
    rs-lem Θ ρ (s e) k = ap S (rs-lem Θ ρ e k)
    rs-lem Θ ρ (rec e e₁ e₂) k = ap3 natrec (rs-lem Θ ρ e₁ k) (λ= (λ n → λ= (λ x₂ → rs-lem-rec Θ ρ e₂ k n x₂))) (rs-lem Θ ρ e k)
    rs-lem Θ ρ (lam e) k = rs-lem' Θ ρ e k (λ= (λ p₁ → rs-lem-abs Θ ρ e k p₁))
    rs-lem Θ ρ (app e e₁) k = ap2 (λ x x₁ → Monotone.f x x₁) (rs-lem Θ ρ e k) (rs-lem Θ ρ e₁ k)
    rs-lem Θ ρ rz k = Refl
    rs-lem Θ ρ (rsuc e) k = ap S (rs-lem Θ ρ e k)
    rs-lem Θ ρ (rrec e e₁ e₂ P) k = ap3 natrec (rs-lem Θ ρ e₁ k) (λ= (λ n → λ= (λ x₂ → {!!}))) (rs-lem Θ ρ e k)
    rs-lem Θ ρ (prod e e₁) k = ap2 (λ x x₁ → x , x₁) (rs-lem Θ ρ e k) (rs-lem Θ ρ e₁ k)
    rs-lem Θ ρ (l-proj e) k = ap fst (rs-lem Θ ρ e k)
    rs-lem Θ ρ (r-proj e) k = ap snd (rs-lem Θ ρ e k)
    rs-lem Θ ρ nil k = Refl
    rs-lem Θ ρ (e ::c e₁) k = ap2 _::_ (rs-lem Θ ρ e k) (rs-lem Θ ρ e₁ k)
    rs-lem Θ ρ (listrec e e₁ e₂) k = ap3 lrec (rs-lem Θ ρ e k) (rs-lem Θ ρ e₁ k) (λ= (λ h → λ= (λ t → λ= (λ x₃ → rs-lem-lrec Θ ρ e₂ k h t x₃))))
    rs-lem Θ ρ true k = Refl
    rs-lem Θ ρ false k = Refl
    rs-lem Θ ρ (max τ e e₁) k = ap2 (Preorder-max-str.max [ τ ]tm) (rs-lem Θ ρ e k) (rs-lem Θ ρ e₁ k)
-}

  extend-sr-once-lemma : ∀ {A B C τ τ'} → (Θ : sctx A B) (ρ : rctx B C) (x : τ ∈ τ' :: C)
                       → _==_ {_} {τ' :: A |- τ} (s-extend (_sr_ Θ ρ) x) (_sr_ (s-extend Θ) (r-extend ρ) x)
  extend-sr-once-lemma Θ ρ i0 = Refl
  extend-sr-once-lemma Θ ρ (iS x) = Refl

  extend-sr-once : ∀ {A B C τ} → (Θ : sctx A B) (ρ : rctx B C)
                 → Id {_} {sctx (τ :: A) (τ :: C)} (s-extend Θ sr r-extend ρ) (s-extend (Θ sr ρ))
  extend-sr-once Θ ρ = λ=i (λ τ → λ= (λ x → ! (extend-sr-once-lemma Θ ρ x)))

  extend-sr-twice : ∀ {A B C τ τ'} → (Θ : sctx A B) (ρ : rctx B C)
                 → Id {_} {sctx (τ' :: τ :: A) (τ' :: τ :: C)}
                   (s-extend (s-extend Θ) sr r-extend (r-extend ρ)) (s-extend (s-extend (Θ sr ρ)))
  extend-sr-twice Θ ρ = ap s-extend (extend-sr-once Θ ρ) ∘ extend-sr-once (s-extend Θ) (r-extend ρ)

  postulate
    sr-lem' : ∀ {Γ Γ' Γ'' τ τ'} → (Θ : sctx Γ Γ') → (ρ : rctx Γ' Γ'') → (e : τ' :: Γ'' |- τ) → (k : fst [ Γ ]c)
            → (λ p₁ → Monotone.f (interpE (subst (ren e (r-extend ρ)) (s-extend Θ))) (k , p₁)) ==
              (λ p₁ → Monotone.f (interpE (subst e (s-extend (λ {τ} x → Θ (ρ x))))) (k , p₁))
            → monotone (λ p₁ → Monotone.f (interpE (subst (ren e (r-extend ρ)) (s-extend Θ))) (k , p₁))
              (λ a b c → Monotone.is-monotone (interpE (subst (ren e (r-extend ρ)) (s-extend Θ))) (k , a) (k , b)
                (Preorder-str.refl (snd [ Γ ]c) k , c)) ==
              monotone (λ p₁ → Monotone.f (interpE (subst e (s-extend (λ {τ} x → Θ (ρ x))))) (k , p₁))
              (λ a b c → Monotone.is-monotone (interpE (subst e (s-extend (λ {τ} x → Θ (ρ x))))) (k , a) (k , b)
                (Preorder-str.refl (snd [ Γ ]c) k , c))

  mutual
    sr-lem-abs : ∀ {Γ Γ' Γ'' τ τ'} → (Θ : sctx Γ Γ') → (ρ : rctx Γ' Γ'') → (e : τ' :: Γ'' |- τ) → (k : fst [ Γ ]c) → (p₁ : fst [ τ' ]t)
               → Monotone.f (interpE (subst (ren e (r-extend ρ)) (s-extend Θ))) (k , p₁) ==
                 Monotone.f (interpE (subst e (s-extend (λ x → Θ (ρ x))))) (k , p₁)
    sr-lem-abs Θ ρ e k p₁ = Monotone.f (interpE (subst (ren e (r-extend ρ)) (s-extend Θ))) (k , p₁) =⟨ sr-lem (s-extend Θ) (r-extend ρ) e (k , p₁) ⟩
                            Monotone.f (interpE (subst e (s-extend Θ sr r-extend ρ))) (k , p₁) =⟨ ap2 Monotone.f (ap interpE (ap (subst e) (extend-sr-once Θ ρ))) Refl ⟩
                            (Monotone.f (interpE (subst e (s-extend (λ x → Θ (ρ x))))) (k , p₁) ∎)

    sr-lem : ∀ {Γ Γ' Γ'' τ} → (Θ : sctx Γ Γ') → (ρ : rctx Γ' Γ'') → (e : Γ'' |- τ) → (k : fst [ Γ ]c)
           → (Monotone.f (interpE (subst (ren e ρ) Θ)) k) == (Monotone.f (interpE (subst e (Θ sr ρ))) k)
    sr-lem Θ ρ unit k = Refl
    sr-lem Θ ρ 0C k = Refl
    sr-lem Θ ρ 1C k = Refl
    sr-lem Θ ρ (plusC e e₁) k =  ap2 _+_ (sr-lem Θ ρ e k) (sr-lem Θ ρ e₁ k)
    sr-lem Θ ρ (var x) k = Refl
    sr-lem Θ ρ z k = Refl
    sr-lem Θ ρ (s e) k = ap S (sr-lem Θ ρ e k)
    sr-lem Θ ρ (rec e e₁ e₂) k = ap3 natrec (sr-lem Θ ρ e₁ k) (λ= (λ n → λ= (λ x₂ → {!!}))) (sr-lem Θ ρ e k)
    sr-lem Θ ρ (lam e) k = sr-lem' Θ ρ e k (λ= (λ p₁ → sr-lem-abs Θ ρ e k p₁))
    sr-lem Θ ρ (app e e₁) k = ap2 (λ x x₁ → Monotone.f x x₁) (sr-lem Θ ρ e k) (sr-lem Θ ρ e₁ k)
    sr-lem Θ ρ rz k = Refl
    sr-lem Θ ρ (rsuc e) k = ap S (sr-lem Θ ρ e k)
    sr-lem Θ ρ (rrec e e₁ e₂ P) k = ap3 natrec (sr-lem Θ ρ e₁ k) (λ= (λ n → λ= (λ x₂ → {!!}))) (sr-lem Θ ρ e k)
    sr-lem Θ ρ (prod e e₁) k = ap2 (λ x x₁ → x , x₁) (sr-lem Θ ρ e k) (sr-lem Θ ρ e₁ k)
    sr-lem Θ ρ (l-proj e) k =  ap fst (sr-lem Θ ρ e k)
    sr-lem Θ ρ (r-proj e) k =  ap snd (sr-lem Θ ρ e k)
    sr-lem Θ ρ nil k = Refl
    sr-lem Θ ρ (e ::c e₁) k =  ap2 _::_ (sr-lem Θ ρ e k) (sr-lem Θ ρ e₁ k)
    sr-lem Θ ρ (listrec e e₁ e₂) k = ap3 lrec (sr-lem Θ ρ e k) (sr-lem Θ ρ e₁ k) (λ= (λ h → λ= (λ t → λ= (λ x₃ → {!!}))))
    sr-lem Θ ρ true k = Refl
    sr-lem Θ ρ false k = Refl
    sr-lem Θ ρ (max τ e e₁) k =  ap2 (Preorder-max-str.max [ τ ]tm) (sr-lem Θ ρ e k) (sr-lem Θ ρ e₁ k)

{-
  postulate
    ss-lem' : ∀ {Γ Γ' Γ'' τ ρ} → (Θ1 : sctx Γ Γ') → (Θ2 : sctx Γ' Γ'') → (e : ρ :: Γ'' |- τ) → (k : fst [ Γ ]c)
            → (λ p₁ → Monotone.f (interpE (subst (subst e (s-extend Θ2)) (s-extend Θ1))) (k , p₁))
              == (λ p₁ → Monotone.f (interpE (subst e (s-extend (λ {τ} x → subst (Θ2 x) Θ1)))) (k , p₁))
            → monotone (λ p₁ → Monotone.f (interpE (subst (subst e (s-extend Θ2)) (s-extend Θ1))) (k , p₁))
              (λ a b c → Monotone.is-monotone (interpE (subst (subst e (s-extend Θ2)) (s-extend Θ1))) (k , a) (k , b)
                (Preorder-str.refl (snd [ Γ ]c) k , c))
              ==
              monotone (λ p₁ → Monotone.f (interpE (subst e (s-extend (λ {τ} x → subst (Θ2 x) Θ1)))) (k , p₁))
              (λ a b c → Monotone.is-monotone (interpE (subst e (s-extend (λ {τ} x → subst (Θ2 x) Θ1)))) (k , a) (k , b)
                (Preorder-str.refl (snd [ Γ ]c) k , c))

  mutual
    ss-abs : ∀ {Γ Γ' Γ'' τ ρ} → (Θ1 : sctx Γ Γ') → (Θ2 : sctx Γ' Γ'') → (e : ρ :: Γ'' |- τ) → (k : fst [ Γ ]c) → (p₁ : fst [ ρ ]t)
           → Monotone.f (interpE (subst (subst e (s-extend (λ {τ} → Θ2))) (s-extend (λ {τ} → Θ1)))) (k , p₁)
             == Monotone.f (interpE (subst e (s-extend (λ {τ} x → subst (Θ2 x) (λ {τ} → Θ1))))) (k , p₁)
    ss-abs Θ1 Θ2 e k p₁ = Monotone.f (interpE (subst (subst e (s-extend Θ2)) (s-extend Θ1))) (k , p₁) =⟨ ss-lem (s-extend Θ1) (s-extend Θ2) e (k , p₁) ⟩
                          Monotone.f (interpE (subst e (s-extend Θ1 ss s-extend Θ2))) (k , p₁) =⟨ {!!} ⟩
                          (Monotone.f (interpE (subst e (s-extend (λ x → subst (Θ2 x) Θ1)))) (k , p₁) ∎)

    ss-lem : ∀ {Γ Γ' Γ'' τ} → (Θ1 : sctx Γ Γ') → (Θ2 : sctx Γ' Γ'') → (e : Γ'' |- τ) → (k : fst [ Γ ]c)
           → (Monotone.f (interpE (subst (subst e Θ2) Θ1)) k) == (Monotone.f (interpE (subst e (Θ1 ss Θ2))) k)
    ss-lem Θ1 Θ2 unit k = Refl
    ss-lem Θ1 Θ2 0C k = Refl
    ss-lem Θ1 Θ2 1C k = Refl
    ss-lem Θ1 Θ2 (plusC e e₁) k = ap2 _+_ (ss-lem Θ1 Θ2 e k) (ss-lem Θ1 Θ2 e₁ k)
    ss-lem Θ1 Θ2 (var x) k = Refl
    ss-lem Θ1 Θ2 z k = Refl
    ss-lem Θ1 Θ2 (s e) k = ap S (ss-lem Θ1 Θ2 e k)
    ss-lem Θ1 Θ2 (rec e e₁ e₂) k = ap3 natrec (ss-lem Θ1 Θ2 e₁ k) (λ= (λ n → λ= (λ x₂ → {!!}))) (ss-lem Θ1 Θ2 e k)
    ss-lem Θ1 Θ2 (lam e) k = ss-lem' Θ1 Θ2 e k (λ= (λ p₁ → ss-abs Θ1 Θ2 e k p₁))
    ss-lem Θ1 Θ2 (app e e₁) k = ap2 (λ x x₁ → Monotone.f x x₁) (ss-lem Θ1 Θ2 e k) (ss-lem Θ1 Θ2 e₁ k)
    ss-lem Θ1 Θ2 rz k = Refl
    ss-lem Θ1 Θ2 (rsuc e) k = ap S (ss-lem Θ1 Θ2 e k)
    ss-lem Θ1 Θ2 (rrec e e₁ e₂ P) k = ap3 natrec (ss-lem Θ1 Θ2 e₁ k) (λ= (λ n → λ= (λ x₂ → {!!}))) (ss-lem Θ1 Θ2 e k)
    ss-lem Θ1 Θ2 (prod e e₁) k = ap2 (λ x x₁ → x , x₁) (ss-lem Θ1 Θ2 e k) (ss-lem Θ1 Θ2 e₁ k)
    ss-lem Θ1 Θ2 (l-proj e) k = ap fst (ss-lem Θ1 Θ2 e k)
    ss-lem Θ1 Θ2 (r-proj e) k = ap snd (ss-lem Θ1 Θ2 e k)
    ss-lem Θ1 Θ2 nil k = Refl
    ss-lem Θ1 Θ2 (e ::c e₁) k = ap2 _::_ (ss-lem Θ1 Θ2 e k) (ss-lem Θ1 Θ2 e₁ k)
    ss-lem Θ1 Θ2 (listrec e e₁ e₂) k = ap3 lrec (ss-lem Θ1 Θ2 e k) (ss-lem Θ1 Θ2 e₁ k) (λ= (λ h → λ= (λ t → λ= (λ x₃ → {!!}))))
    ss-lem Θ1 Θ2 true k = Refl
    ss-lem Θ1 Θ2 false k = Refl
    ss-lem Θ1 Θ2 (max τ e e₁) k = ap2 (Preorder-max-str.max [ τ ]tm) (ss-lem Θ1 Θ2 e k) (ss-lem Θ1 Θ2 e₁ k)
-}
{-
  subst-comp-lem : ∀ {Γ Γ' τ τ'} → (Θ : sctx Γ Γ') → (v : Γ |- τ') → (e : τ' :: Γ' |- τ) → (k : fst [ Γ ]c)
                 → (Monotone.f (interpE (subst (subst e (s-extend Θ)) (q v))) k) == (Monotone.f (interpE (subst e (lem3' Θ v))) k)
  subst-comp-lem Θ v e k = {!!}

  subst-comp2-lem : ∀ {Γ Γ' τ τ1 τ2} → (Θ : sctx Γ Γ') → (v1 : Γ |- τ1) → (v2 : Γ |- τ2) → (e1 : τ1 :: τ2 :: Γ' |- τ) → (k : fst [ Γ ]c)
                  → (Monotone.f (interpE (subst (subst e1 (s-extend (s-extend Θ))) (lem4 v1 v2))) k) == (Monotone.f (interpE (subst e1 (lem4' Θ v1 v2))) k)
  subst-comp2-lem Θ v1 v2 e1 k = {!!}

  subst-comp3-lem : ∀ {Γ Γ' τ τ1 τ2} → (Θ : sctx Γ Γ') → (v1 : Γ' |- τ1) → (v2 : Γ' |- τ2) → (e1 : τ1 :: τ2 :: Γ' |- τ) → (k : fst [ Γ ]c)
                  → (Monotone.f (interpE (subst (subst e1 (lem4 v1 v2)) Θ)) k) == (Monotone.f (interpE (subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ)))) k)
  subst-comp3-lem Θ v1 v2 e1 k = {!!}

  subst-comp4-lem : ∀ {Γ Γ' τ τ1 τ2 τ3} → (Θ : sctx Γ Γ') → (v1 : Γ |- τ1) → (v2 : Γ |- τ2) → (v3 : Γ |- τ3) → (e : τ1 :: τ2 :: τ3 :: Γ' |- τ) → (k : fst [ Γ ]c)
                  → (Monotone.f (interpE (subst (subst e (s-extend (s-extend (s-extend Θ)))) (lem5 v1 v2 v3))) k) == (Monotone.f (interpE (subst e (lem5' Θ v1 v2 v3))) k)
  subst-comp4-lem Θ v1 v2 v3 e k = {!!}

  cong-with-ren : ∀ {Γ Γ' τ} → (e : Γ' |- τ) → (ρ : rctx Γ Γ') → (k : fst [ Γ ]c)
                → Monotone.f (interpE (ren e ρ)) k == Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
                → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (ren e ρ)) k) (Monotone.f (interpE e) (Monotone.f (interpR ρ) k))
  cong-with-ren {τ = unit} e ρ k p = <>
  cong-with-ren {τ = nat} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren {Γ} {Γ'} {nat} e ρ k Refl | m | .m = ♭nat-refl m
  cong-with-ren {τ = τ ->c τ₁} e ρ k p x with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren {Γ} {Γ'} {τ ->c τ₁} e ρ k Refl x | f1 | .f1 = mono-refl (snd [ τ ]t) (snd [ τ₁ ]t) f1 x
  cong-with-ren {τ = τ ×c τ₁} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren {Γ} {Γ'} {τ ×c τ₁} e ρ k Refl | p1 | .p1 = axb-refl (snd [ τ ]t) (snd [ τ₁ ]t) p1
  cong-with-ren {τ = list τ} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren {Γ} {Γ'} {list τ} e ρ k Refl | l1 | .l1 = l-refl (snd [ τ ]t) l1
  cong-with-ren {τ = bool} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren {Γ} {Γ'} {bool} e ρ k Refl | b | .b = b-refl b
  cong-with-ren {τ = C} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren {Γ} {Γ'} {C} e ρ k Refl | m | .m = nat-refl m
  cong-with-ren {τ = rnat} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren {Γ} {Γ'} {rnat} e ρ k Refl | m | .m = nat-refl m

  cong-with-ren' : ∀ {Γ Γ' τ} → (e : Γ' |- τ) → (ρ : rctx Γ Γ') → (k : fst [ Γ ]c)
                 → Monotone.f (interpE (ren e ρ)) k == Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
                 → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE e) (Monotone.f (interpR ρ) k)) (Monotone.f (interpE (ren e ρ)) k)
  cong-with-ren' {τ = unit} e ρ k p = <>
  cong-with-ren' {τ = nat} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren' {Γ} {Γ'} {nat} e ρ k Refl | m | .m = ♭nat-refl m
  cong-with-ren' {τ = τ ->c τ₁} e ρ k p x with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren' {Γ} {Γ'} {τ ->c τ₁} e ρ k Refl x | f1 | .f1 = mono-refl (snd [ τ ]t) (snd [ τ₁ ]t) f1 x
  cong-with-ren' {τ = τ ×c τ₁} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren' {Γ} {Γ'} {τ ×c τ₁} e ρ k Refl | p1 | .p1 = axb-refl (snd [ τ ]t) (snd [ τ₁ ]t) p1
  cong-with-ren' {τ = list τ} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren' {Γ} {Γ'} {list τ} e ρ k Refl | l1 | .l1 = l-refl (snd [ τ ]t) l1
  cong-with-ren' {τ = bool} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren' {Γ} {Γ'} {bool} e ρ k Refl | b | .b = b-refl b
  cong-with-ren' {τ = C} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren' {Γ} {Γ'} {C} e ρ k Refl | m | .m = nat-refl m
  cong-with-ren' {τ = rnat} e ρ k p with (Monotone.f (interpE (ren e ρ)) k) | Monotone.f (interpE e) (Monotone.f (interpR ρ) k)
  cong-with-ren' {Γ} {Γ'} {rnat} e ρ k Refl | m | .m = nat-refl m

  cong-with-subst : ∀ {Γ Γ' τ} → (e : Γ' |- τ) → (Θ : sctx Γ Γ') → (k : fst [ Γ ]c)
                  → Monotone.f (interpE (subst e Θ)) k == Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
                  → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE (subst e Θ)) k) (Monotone.f (interpE e) (Monotone.f (interpS Θ) k))
  cong-with-subst {τ = unit} e Θ k p = <>
  cong-with-subst {τ = nat} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst {Γ} {Γ'} {nat} e Θ k Refl | m | .m = ♭nat-refl m
  cong-with-subst {τ = τ ->c τ₁} e Θ k p x with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst {Γ} {Γ'} {τ ->c τ₁} e Θ k Refl x | f1 | .f1 = mono-refl (snd [ τ ]t) (snd [ τ₁ ]t) f1 x
  cong-with-subst {τ = τ ×c τ₁} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst {Γ} {Γ'} {τ ×c τ₁} e Θ k Refl | p1 | .p1 = axb-refl (snd [ τ ]t) (snd [ τ₁ ]t) p1
  cong-with-subst {τ = list τ} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst {Γ} {Γ'} {list τ} e Θ k Refl | l1 | .l1 = l-refl (snd [ τ ]t) l1
  cong-with-subst {τ = bool} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst {Γ} {Γ'} {bool} e Θ k Refl | b | .b = b-refl b
  cong-with-subst {τ = C} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst {Γ} {Γ'} {C} e Θ k Refl | m | .m = nat-refl m
  cong-with-subst {τ = rnat} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst {Γ} {Γ'} {rnat} e Θ k Refl | m | .m = nat-refl m

  cong-with-subst' : ∀ {Γ Γ' τ} → (e : Γ' |- τ) → (Θ : sctx Γ Γ') → (k : fst [ Γ ]c)
                   → Monotone.f (interpE (subst e Θ)) k == Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
                   → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE e) (Monotone.f (interpS Θ) k)) (Monotone.f (interpE (subst e Θ)) k)
  cong-with-subst' {τ = unit} e Θ k p = <>
  cong-with-subst' {τ = nat} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst' {Γ} {Γ'} {nat} e Θ k Refl | m | .m = ♭nat-refl m
  cong-with-subst' {τ = τ ->c τ₁} e Θ k p x with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst' {Γ} {Γ'} {τ ->c τ₁} e Θ k Refl x | f1 | .f1 = mono-refl (snd [ τ ]t) (snd [ τ₁ ]t) f1 x
  cong-with-subst' {τ = τ ×c τ₁} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst' {Γ} {Γ'} {τ ×c τ₁} e Θ k Refl | p1 | .p1 = axb-refl (snd [ τ ]t) (snd [ τ₁ ]t) p1
  cong-with-subst' {τ = list τ} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst' {Γ} {Γ'} {list τ} e Θ k Refl | l1 | .l1 = l-refl (snd [ τ ]t) l1
  cong-with-subst' {τ = bool} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst' {Γ} {Γ'} {bool} e Θ k Refl | b | .b = b-refl b
  cong-with-subst' {τ = C} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst' {Γ} {Γ'} {C} e Θ k Refl | m | .m = nat-refl m
  cong-with-subst' {τ = rnat} e Θ k p with (Monotone.f (interpE (subst e Θ)) k) | Monotone.f (interpE e) (Monotone.f (interpS Θ) k)
  cong-with-subst' {Γ} {Γ'} {rnat} e Θ k Refl | m | .m = nat-refl m

  cong : ∀ {Γ τ} → (e e' : Γ |- τ) → (k : fst [ Γ ]c) → Monotone.f (interpE e) k == Monotone.f (interpE e') k
       → Preorder-str.≤ (snd [ τ ]t) (Monotone.f (interpE e) k) (Monotone.f (interpE e') k)
  cong {τ = unit} e e' k p = <>
  cong {τ = nat} e e' k p with (Monotone.f (interpE e) k) | (Monotone.f (interpE e') k)
  cong {Γ} {nat} e e' k Refl | Z | .Z = <>
  cong {Γ} {nat} e e' k Refl | S m | S .m = ♭nat-refl m
  cong {τ = τ ->c τ₁} e e' k p x with (Monotone.f (interpE e) k) | (Monotone.f (interpE e') k) 
  cong {Γ} {τ ->c τ₁} e e' k Refl x | monotone f f-is-monotone | monotone .f .f-is-monotone = Preorder-str.refl (snd [ τ₁ ]t) (f x)
  cong {τ = τ ×c τ₁} e e' k p with (Monotone.f (interpE e) k) | (Monotone.f (interpE e') k)
  cong {Γ} {τ ×c τ₁} e e' k Refl | a , b | .(a , b) = (Preorder-str.refl (snd [ τ ]t) a) , (Preorder-str.refl (snd [ τ₁ ]t) b)
  cong {τ = list τ} e e' k p with (Monotone.f (interpE e) k) | (Monotone.f (interpE e') k) 
  cong {Γ} {list τ} e e' k Refl | [] | .[] = <>
  cong {Γ} {list τ} e e' k Refl | x :: c | .x :: .c = (Preorder-str.refl (snd [ τ ]t) x) , l-refl (snd [ τ ]t) c
  cong {τ = bool} e e' k p with (Monotone.f (interpE e) k) | (Monotone.f (interpE e') k)
  cong {Γ} {bool} e e' k Refl | True | .True = <>
  cong {Γ} {bool} e e' k Refl | False | .False = <>
  cong {τ = C} e e' k p with (Monotone.f (interpE e) k) | (Monotone.f (interpE e') k) 
  cong {Γ} {C} e e' k Refl | Z | .Z = <>
  cong {Γ} {C} e e' k Refl | S m | S .m = nat-refl m
  cong {τ = rnat} e e' k p with (Monotone.f (interpE e) k) | (Monotone.f (interpE e') k) 
  cong {Γ} {rnat} e e' k Refl | Z | .Z = <>
  cong {Γ} {rnat} e e' k Refl | S m | S .m = nat-refl m

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
        (cong-with-ren e1 ρ k (ren-eq-lem ρ e1 k))
        (Preorder-str.trans (snd [ τ ]t)
        (Monotone.f (interpE e1) (Monotone.f (interpR ρ) k))
        (Monotone.f (interpE e2) (Monotone.f (interpR ρ) k))
        (Monotone.f (interpE (ren e2 ρ)) k)
          (sound e1 e2 d (Monotone.f (interpR ρ) k))
          (cong-with-ren' e2 ρ k (ren-eq-lem ρ e2 k)))
  sound {Γ} {τ} ._ ._ (subst-cong {.Γ} {Γ'} {.τ} {e1} {e2} {Θ} d) k =
    Preorder-str.trans (snd [ τ ]t)
      (Monotone.f (interpE (subst e1 Θ)) k)
      (Monotone.f (interpE e1) (Monotone.f (interpS Θ) k))
      (Monotone.f (interpE (subst e2 Θ)) k)
        (cong-with-subst e1 Θ k (subst-eq-lem Θ e1 k))
        (Preorder-str.trans (snd [ τ ]t)
          (Monotone.f (interpE e1) (Monotone.f (interpS Θ) k))
          (Monotone.f (interpE e2) (Monotone.f (interpS Θ) k))
          (Monotone.f (interpE (subst e2 Θ)) k)
            (sound e1 e2 d (Monotone.f (interpS Θ) k))
            (cong-with-subst' e2 Θ k (subst-eq-lem Θ e2 k)))
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
  sound .(ren (ren e ρ2) ρ1) ._ (ren-comp-l ρ1 ρ2 e) k = cong (ren (ren e ρ2) ρ1) (ren e (ρ1 ∙rr ρ2)) k (ren-comp-lem ρ1 ρ2 e k)
  sound ._ .(ren (ren e ρ2) ρ1) (ren-comp-r ρ1 ρ2 e) k = cong (ren e (ρ1 ∙rr ρ2)) (ren (ren e ρ2) ρ1) k (! (ren-comp-lem ρ1 ρ2 e k))
  sound {Γ} {τ} e ._ (subst-id-l {.Γ} {.τ} .e) k = cong e (subst e ids) k (subst-id-lem e k)
  sound ._ e' (subst-id-r .e') k = cong (subst e' ids) e' k (! (subst-id-lem e' k))
  sound .(ren (subst e Θ) ρ) ._ (subst-rs-l ρ Θ e) k = cong (ren (subst e Θ) ρ) (subst e (ρ rs Θ)) k (rs-lem Θ ρ e k)
  sound ._ .(ren (subst e Θ) ρ) (subst-rs-r ρ Θ e) k = cong (subst e (ρ rs Θ)) (ren (subst e Θ) ρ) k (! (rs-lem Θ ρ e k))
  sound .(subst (ren e ρ) Θ) ._ (subst-sr-l Θ ρ e) k = cong (subst (ren e ρ) Θ) (subst e (Θ sr ρ)) k (sr-lem Θ ρ e k)
  sound ._ .(subst (ren e ρ) Θ) (subst-sr-r Θ ρ e) k = cong (subst e (Θ sr ρ)) (subst (ren e ρ) Θ) k (! (sr-lem Θ ρ e k))
  sound ._ .(subst (subst e Θ2) Θ1) (subst-ss-l Θ1 Θ2 e) k = cong (subst e (Θ1 ss Θ2)) (subst (subst e Θ2) Θ1) k (! (ss-lem Θ1 Θ2 e k))
  sound .(subst (subst e Θ2) Θ1) ._ (subst-ss-r Θ1 Θ2 e) k = cong (subst (subst e Θ2) Θ1) (subst e (Θ1 ss Θ2)) k (ss-lem Θ1 Θ2 e k)
  sound ._ .(subst e (lem3' Θ v)) (subst-compose-l Θ v e) k = cong (subst (subst e (s-extend Θ)) (q v)) (subst e (lem3' Θ v)) k (subst-comp-lem Θ v e k)
  sound .(subst e (lem3' Θ v)) ._ (subst-compose-r Θ v e) k = cong (subst e (lem3' Θ v)) (subst (subst e (s-extend Θ)) (q v)) k (! (subst-comp-lem Θ v e k))
  sound ._ .(subst e1 (lem3' (lem3' Θ v2) v1)) (subst-compose2-l Θ e1 v1 v2) k =
    cong (subst (subst e1 (s-extend (s-extend Θ))) (lem4 v1 v2)) (subst e1 (lem4' Θ v1 v2)) k (subst-comp2-lem Θ v1 v2 e1 k)
  sound .(subst e1 (lem3' (lem3' Θ v2) v1)) ._ (subst-compose2-r Θ e1 v1 v2) k =
    cong (subst e1 (lem4' Θ v1 v2)) (subst (subst e1 (s-extend (s-extend Θ))) (lem4 v1 v2)) k (! (subst-comp2-lem Θ v1 v2 e1 k))
  sound ._ .(subst e1 (lem3' (lem3' Θ (subst v2 Θ)) (subst v1 Θ))) (subst-compose3-l Θ e1 v1 v2) k =
    cong (subst (subst e1 (lem4 v1 v2)) Θ) (subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ))) k (subst-comp3-lem Θ v1 v2 e1 k)
  sound .(subst e1 (lem3' (lem3' Θ (subst v2 Θ)) (subst v1 Θ))) ._ (subst-compose3-r Θ e1 v1 v2) k =
    cong (subst e1 (lem4' Θ (subst v1 Θ) (subst v2 Θ))) (subst (subst e1 (lem4 v1 v2)) Θ) k (! (subst-comp3-lem Θ v1 v2 e1 k))
  sound ._ .(subst e2 (lem3' (lem3' Θ r) v')) (subst-compose4-l Θ v' r e2) k =
    cong (subst (subst e2 (s-extend (s-extend Θ))) (lem4 v' r)) (subst e2 (lem4' Θ v' r)) k (subst-comp2-lem Θ v' r e2 k)
  sound .(subst e2 (lem3' (lem3' Θ r) v')) ._ (subst-compose4-r Θ v' r e2) k =
    cong (subst e2 (lem4' Θ v' r)) (subst (subst e2 (s-extend (s-extend Θ))) (lem4 v' r)) k (! (subst-comp2-lem Θ v' r e2 k))
  sound ._ .(subst e (lem3' (lem3' (lem3' Θ v3) v2) v1)) (subst-compose5-l Θ e v1 v2 v3) k =
    cong (subst (subst e (s-extend (s-extend (s-extend Θ)))) (lem5 v1 v2 v3)) (subst e (lem5' Θ v1 v2 v3)) k (subst-comp4-lem Θ v1 v2 v3 e k)
  sound .(subst e (lem3' (lem3' (lem3' Θ v3) v2) v1)) ._ (subst-compose5-r Θ e v1 v2 v3) k =
    cong (subst e (lem5' Θ v1 v2 v3)) (subst (subst e (s-extend (s-extend (s-extend Θ)))) (lem5 v1 v2 v3)) k (! (subst-comp4-lem Θ v1 v2 v3 e k))
-}
  sound = {!!}

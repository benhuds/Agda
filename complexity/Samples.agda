{- SAMPLE PROGRAMS IN SOURCE LANGUAGE -}

open import Preliminaries
open import Source

module Samples where

  -- dbl (n : nat) : nat = 2 * n
  dbl : ∀ {Γ} → Γ |- (nat ->s nat)
  dbl = lam (rec (var i0) z (suc (suc (force (var (iS i0))))))
 
  -- add (m n : nat) : nat = m + n
  add : ∀ {Γ} → Γ |- (nat ->s (nat ->s nat))
  add = lam (lam (rec (var (iS i0)) (var i0) (suc (force (var (iS i0))))))

  -- mult (m n : nat) : nat = m * n
  mult : ∀ {Γ} → Γ |- (nat ->s (nat ->s nat))
  mult = lam (lam (rec (var (iS i0)) z (app (app add (var (iS (iS i0)))) (force (var (iS i0))))))

  -- hack : instead of having bool case analysis just do natural number recursion and return 1/0

  -- iszero (n : nat) : nat = z -> 1 | _ -> 0
  isz : ∀ {Γ} → Γ |- (nat ->s nat)
  isz = lam (rec (var i0) (suc z) z)

  -- leq (m n : nat) : nat = m ≤ n
  leq : ∀ {Γ} → Γ |- (nat ->s (nat ->s nat))
  leq = lam (lam (rec (var (iS i0))
          (app isz (var (iS i0)))
          (rec (var (iS (iS (iS i0)))) (suc z) (force (var (iS i0))))))

  -- len (l : list τ) : nat = [] -> z | x :: xs -> 1 + len xs
  len : ∀ {Γ τ} → Γ |- (list τ ->s nat)
  len = lam (listrec (var i0) z (suc (force (var (iS (iS i0))))))

  -- insert (l : list nat) (n : nat) : list nat = [] -> [el] | x :: xs -> (leq el x -> el :: x :: xs | x :: (insert el xs))
  insert : ∀ {Γ} → Γ |- (list nat ->s (nat ->s list nat))
  insert = lam (lam (listrec (var (iS i0))
             (var i0 ::s nil)
             (rec (app (app leq (var (iS (iS (iS i0))))) (var i0))
               (var (iS (iS (iS i0))) ::s var (iS (iS (iS (iS i0)))))
               (var i0 ::s force (var (iS (iS (iS (iS i0)))))))))

  -- insertion sort (l : list nat) : list nat = [] -> [] | x :: xs -> insert x (isort xs)
  isort : ∀ {Γ} → Γ |- (list nat ->s list nat)
  isort = lam (listrec (var i0) nil (app (app insert (force (var (iS (iS i0))))) (var i0)))

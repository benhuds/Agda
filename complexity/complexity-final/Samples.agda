{- SAMPLE PROGRAMS IN SOURCE LANGUAGE -}

{-# OPTIONS --no-termination-check #-}

open import Preliminaries
open import Source
open import Pilot2
open import Translation
open import Interp
open import Preorder

module Samples where

  s2r : ∀ {Γ τ} → Γ Source.|- τ → el ([ (⟨⟨ Γ ⟩⟩c) ]c ->p [ (|| τ ||) ]t)
  s2r p = interpE || p ||e

  -- this works
  {- dbl (n : nat) : nat = 2 * n -}
  dbl : ∀ {Γ} → Γ Source.|- (nat ->s nat)
  dbl = lam (rec (var i0) z (suc (suc (force (var (iS i0))))))

  -- this works
  {- add (m n : nat) : nat = m + n -}
  add : ∀ {Γ} → Γ Source.|- (nat ->s (nat ->s nat))
  add = lam (lam (rec (var (iS i0)) (var i0) (suc (force (var (iS i0))))))

  -- this works
  {- mult (m n : nat) : nat = m * n -}
  mult : ∀ {Γ} → Γ Source.|- (nat ->s (nat ->s nat))
  mult = lam (lam (rec (var (iS i0)) z (app (app add (var (iS (iS i0)))) (force (var (iS i0))))))

  -- this works
  {- pred (n : nat) : nat = predecessor of n -}
  pred : ∀ {Γ} → Γ Source.|- (nat ->s nat)
  pred = lam (rec (var i0) z (var i0))

  -- this works if you don't have termination check
  {- fib (n : nat) : nat = computes the nth fibonacci number (naive) -}
  fib : ∀ {Γ} → Γ Source.|- (nat ->s nat)
  fib = lam (rec (var i0) (suc z) (rec (var i0) (suc z) (app (app add (app fib (var i0))) (app fib (var (iS (iS i0)))))))

  -- hack : instead of having bool case analysis just do natural number recursion and return 1/0

  -- this works
  {- iszero (n : nat) : nat = z -> 1 | _ -> 0 -}
  isz : ∀ {Γ} → Γ Source.|- (nat ->s nat)
  isz = lam (rec (var i0) (suc z) z)

  {- leq (m n : nat) : nat = m ≤ n -}
  leq : ∀ {Γ} → Γ Source.|- (nat ->s (nat ->s nat))
  leq = lam (lam (rec (var (iS i0)) (suc z)
          (rec (var (iS (iS i0))) z (app (app leq (var (iS (iS i0)))) (var i0)))))

  -- works but needs termination off
  {- eq (m n : nat) : nat = m = n -}
  eq : ∀ {Γ} → Γ Source.|- (nat ->s (nat ->s nat))
  eq = lam (lam (rec (var (iS i0)) (app isz (var i0)) (rec (var (iS (iS i0))) z (app (app eq (var (iS (iS i0)))) (var i0)))))

  -- this works
  {- len (l : list τ) : nat = [] -> z | x :: xs -> 1 + len xs -}
  len : ∀ {Γ τ} → Γ Source.|- (list τ ->s nat)
  len = lam (listrec (var i0) z (suc (force (var (iS (iS i0))))))

  -- this works but needs terminaion off for eq
  {- nth (n : nat) (l : list τ) : nat = [] -> 1 | x :: xs -> if n = x then 0 else 1 + (nth n xs) -}
  nth : ∀ {Γ} → Γ Source.|- (list nat ->s (nat ->s nat))
  nth = lam (lam (listrec (var (iS i0)) (suc z) (rec (app (app eq (var (iS (iS (iS i0))))) (var i0)) (suc (force (var (iS (iS i0))))) z)))

  -- this works
  {- append (l1 l2 : list τ) : list τ = match l1 with [] -> l2 | x :: xs -> x :: (append xs ys) -}
  append : ∀ {Γ τ} → Γ Source.|- (list τ ->s (list τ ->s list τ))
  append = lam (lam (listrec (var (iS i0)) (var i0) (var i0 ::s force (var (iS (iS i0))))))

  -- need to redo these indices i think i messed something up
  {- insert (l : list nat) (el : nat) : list nat = [] -> [el] | x :: xs -> (leq el x -> el :: x :: xs | x :: (insert el xs)) -}
  insert : ∀ {Γ} → Γ Source.|- (list nat ->s (nat ->s list nat))
  insert = lam (lam (listrec (var (iS i0))
             (var i0 ::s nil)
             (rec (app (app leq (var (iS (iS (iS i0))))) (var i0))
               (var i0 ::s force (var (iS (iS i0))))
               (var (iS (iS (iS (iS (iS i0))))) ::s var (iS (iS (iS (iS (iS (iS i0))))))))))

  {- insertion sort (l : list nat) : list nat = [] -> [] | x :: xs -> insert x (isort xs) -}
  isort : ∀ {Γ} → Γ Source.|- (list nat ->s list nat)
  isort = lam (listrec (var i0) nil (app (app insert (force (var (iS (iS i0))))) (var i0)))

  -- this works
  {- map (l : list τ) (f : τ → τ) : list τ = [] -> [] | x :: xs -> f x :: map f xs -}
  map : ∀ {Γ τ} → Γ Source.|- ((τ ->s τ) ->s (list τ ->s list τ))
  map = lam (lam (listrec (var i0) nil (app (var (iS (iS (iS (iS i0))))) (var i0) ::s force (var (iS (iS i0))))))

  dbl-trans : ∀ {Γ τ} → {!!} --el ([ (⟨⟨ Γ ⟩⟩c) ]c ->p [ (|| τ ||) ]t)
  dbl-trans {Γ} = {!s2r (app (app leq (suc (suc z))) (suc (suc z)))!}

  example1 : ∀ {Γ τ} → {!!}
  example1 {Γ} {τ} = {!!} --copy and paste from this goal to the thing below
{-
  dbl-trans : ∀ {Γ} → ⟨⟨ Γ ⟩⟩c Pilot2.|- || nat ->s nat ||
  dbl-trans = prod 0C
                                     (lam
                                      (prod
                                       (plusC (l-proj (prod 0C (var i0)))
                                        (l-proj
                                         (rec (r-proj (prod 0C (var i0)))
                                          (prod (plusC 1C (l-proj (prod 0C z))) (r-proj (prod 0C z)))
                                          (prod
                                           (plusC 1C
                                            (l-proj
                                             (prod
                                              (l-proj
                                               (prod
                                                (l-proj
                                                 (prod
                                                  (plusC (l-proj (prod 0C (var (iS i0))))
                                                   (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                  (r-proj (r-proj (prod 0C (var (iS i0)))))))
                                                (s
                                                 (r-proj
                                                  (prod
                                                   (plusC (l-proj (prod 0C (var (iS i0))))
                                                    (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                   (r-proj (r-proj (prod 0C (var (iS i0))))))))))
                                              (s
                                               (r-proj
                                                (prod
                                                 (l-proj
                                                  (prod
                                                   (plusC (l-proj (prod 0C (var (iS i0))))
                                                    (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                   (r-proj (r-proj (prod 0C (var (iS i0)))))))
                                                 (s
                                                  (r-proj
                                                   (prod
                                                    (plusC (l-proj (prod 0C (var (iS i0))))
                                                     (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                    (r-proj (r-proj (prod 0C (var (iS i0))))))))))))))
                                           (r-proj
                                            (prod
                                             (l-proj
                                              (prod
                                               (l-proj
                                                (prod
                                                 (plusC (l-proj (prod 0C (var (iS i0))))
                                                  (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                 (r-proj (r-proj (prod 0C (var (iS i0)))))))
                                               (s
                                                (r-proj
                                                 (prod
                                                  (plusC (l-proj (prod 0C (var (iS i0))))
                                                   (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                  (r-proj (r-proj (prod 0C (var (iS i0))))))))))
                                             (s
                                              (r-proj
                                               (prod
                                                (l-proj
                                                 (prod
                                                  (plusC (l-proj (prod 0C (var (iS i0))))
                                                   (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                  (r-proj (r-proj (prod 0C (var (iS i0)))))))
                                                (s
                                                 (r-proj
                                                  (prod
                                                   (plusC (l-proj (prod 0C (var (iS i0))))
                                                    (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                   (r-proj (r-proj (prod 0C (var (iS i0)))))))))))))))))
                                       (r-proj
                                        (rec (r-proj (prod 0C (var i0)))
                                         (prod (plusC 1C (l-proj (prod 0C z))) (r-proj (prod 0C z)))
                                         (prod
                                          (plusC 1C
                                           (l-proj
                                            (prod
                                             (l-proj
                                              (prod
                                               (l-proj
                                                (prod
                                                 (plusC (l-proj (prod 0C (var (iS i0))))
                                                  (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                 (r-proj (r-proj (prod 0C (var (iS i0)))))))
                                               (s
                                                (r-proj
                                                 (prod
                                                  (plusC (l-proj (prod 0C (var (iS i0))))
                                                   (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                  (r-proj (r-proj (prod 0C (var (iS i0))))))))))
                                             (s
                                              (r-proj
                                               (prod
                                                (l-proj
                                                 (prod
                                                  (plusC (l-proj (prod 0C (var (iS i0))))
                                                   (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                  (r-proj (r-proj (prod 0C (var (iS i0)))))))
                                                (s
                                                 (r-proj
                                                  (prod
                                                   (plusC (l-proj (prod 0C (var (iS i0))))
                                                    (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                   (r-proj (r-proj (prod 0C (var (iS i0))))))))))))))
                                          (r-proj
                                           (prod
                                            (l-proj
                                             (prod
                                              (l-proj
                                               (prod
                                                (plusC (l-proj (prod 0C (var (iS i0))))
                                                 (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                (r-proj (r-proj (prod 0C (var (iS i0)))))))
                                              (s
                                               (r-proj
                                                (prod
                                                 (plusC (l-proj (prod 0C (var (iS i0))))
                                                  (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                 (r-proj (r-proj (prod 0C (var (iS i0))))))))))
                                            (s
                                             (r-proj
                                              (prod
                                               (l-proj
                                                (prod
                                                 (plusC (l-proj (prod 0C (var (iS i0))))
                                                  (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                 (r-proj (r-proj (prod 0C (var (iS i0)))))))
                                               (s
                                                (r-proj
                                                 (prod
                                                  (plusC (l-proj (prod 0C (var (iS i0))))
                                                   (l-proj (r-proj (prod 0C (var (iS i0))))))
                                                  (r-proj (r-proj (prod 0C (var (iS i0))))))))))))))))))

  aaa : ∀ {Γ} → interpE (r-proj (dbl-trans {Γ})) == {!!}
  aaa = {!!}

  interp-dbl-trans : ∀ {Γ} → Monotone (fst [ ⟨⟨ Γ ⟩⟩c ]c) (fst [ ⟨⟨ nat ->s nat ⟩⟩ ]t) (snd [ ⟨⟨ Γ ⟩⟩c ]c) (snd [ ⟨⟨ nat ->s nat ⟩⟩ ]t)
  interp-dbl-trans {Γ} = monotone
                           (λ x →
                              monotone
                              (λ p₁ →
                                 (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) p₁))
                              (λ a b c →
                                 nat-trans
                                 (fst (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) a))
                                 (fst (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) b))
                                 (fst (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) b))
                                 (fst
                                  (♭h-fix-args (monotone (λ x₁ → 1 , 0) (λ x₁ y z₁ → <> , <>))
                                   (monotone
                                    (λ x₁ → S (fst (snd (fst x₁))) , S (S (snd (snd (fst x₁)))))
                                    (λ x₁ y z₁ → fst (snd (fst z₁)) , snd (snd (fst z₁))))
                                   ((x , a) , a) ((x , b) , b) c))
                                 (fst
                                  (♭h-fix-el (monotone (λ x₁ → 1 , 0) (λ x₁ y z₁ → <> , <>))
                                   (monotone
                                    (λ x₁ → S (fst (snd (fst x₁))) , S (S (snd (snd (fst x₁)))))
                                    (λ x₁ y z₁ → fst (snd (fst z₁)) , snd (snd (fst z₁))))
                                   ((x , a) , a) ((x , b) , b)
                                   ((Preorder-str.refl (snd [ ⟨⟨ Γ ⟩⟩c ]c) x , c) , c)))
                                 ,
                                 ♭nat-trans
                                 (snd (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) a))
                                 (snd (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) b))
                                 (snd (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) b))
                                 (snd
                                  (♭h-fix-args (monotone (λ x₁ → 1 , 0) (λ x₁ y z₁ → <> , <>))
                                   (monotone
                                    (λ x₁ → S (fst (snd (fst x₁))) , S (S (snd (snd (fst x₁)))))
                                    (λ x₁ y z₁ → fst (snd (fst z₁)) , snd (snd (fst z₁))))
                                   ((x , a) , a) ((x , b) , b) c))
                                 (snd
                                  (♭h-fix-el (monotone (λ x₁ → 1 , 0) (λ x₁ y z₁ → <> , <>))
                                   (monotone
                                    (λ x₁ → S (fst (snd (fst x₁))) , S (S (snd (snd (fst x₁)))))
                                    (λ x₁ y z₁ → fst (snd (fst z₁)) , snd (snd (fst z₁))))
                                   ((x , a) , a) ((x , b) , b)
                                   ((Preorder-str.refl (snd [ ⟨⟨ Γ ⟩⟩c ]c) x , c) , c)))))
                           (λ x y z₁ w →
                              nat-trans
                              (fst (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) w))
                              (fst (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) w))
                              (fst (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) w))
                              (fst
                               (♭h-fix-args (monotone (λ x₁ → 1 , 0) (λ x₁ y₁ z₂ → <> , <>))
                                (monotone
                                 (λ x₁ → S (fst (snd (fst x₁))) , S (S (snd (snd (fst x₁)))))
                                 (λ x₁ y₁ z₂ → fst (snd (fst z₂)) , snd (snd (fst z₂))))
                                ((x , w) , w) ((y , w) , w) (♭nat-refl w)))
                              (fst
                               (♭h-fix-el (monotone (λ x₁ → 1 , 0) (λ x₁ y₁ z₂ → <> , <>))
                                (monotone
                                 (λ x₁ → S (fst (snd (fst x₁))) , S (S (snd (snd (fst x₁)))))
                                 (λ x₁ y₁ z₂ → fst (snd (fst z₂)) , snd (snd (fst z₂))))
                                ((x , w) , w) ((y , w) , w) ((z₁ , ♭nat-refl w) , ♭nat-refl w)))
                              ,
                              ♭nat-trans
                              (snd (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) w))
                              (snd (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) w))
                              (snd (natrec (1 , 0) (λ n x₂ → S (fst x₂) , S (S (snd x₂))) w))
                              (snd
                               (♭h-fix-args (monotone (λ x₁ → 1 , 0) (λ x₁ y₁ z₂ → <> , <>))
                                (monotone
                                 (λ x₁ → S (fst (snd (fst x₁))) , S (S (snd (snd (fst x₁)))))
                                 (λ x₁ y₁ z₂ → fst (snd (fst z₂)) , snd (snd (fst z₂))))
                                ((x , w) , w) ((y , w) , w) (♭nat-refl w)))
                              (snd
                               (♭h-fix-el (monotone (λ x₁ → 1 , 0) (λ x₁ y₁ z₂ → <> , <>))
                                (monotone
                                 (λ x₁ → S (fst (snd (fst x₁))) , S (S (snd (snd (fst x₁)))))
                                 (λ x₁ y₁ z₂ → fst (snd (fst z₂)) , snd (snd (fst z₂))))
                                ((x , w) , w) ((y , w) , w) ((z₁ , ♭nat-refl w) , ♭nat-refl w))))
-} 

  {- halve (l : list nat) : (list nat * list nat) = splits a list in half -}
  halve : ∀ {Γ} → Γ Source.|- (list nat ->s (list nat ×s list nat))
  halve = lam (listrec (var i0)
            (prod nil nil)
            (listrec (var (iS i0))
              (prod (var i0 ::s nil) nil)
              (prod (var (iS (iS (iS i0))) ::s split (force (var (iS (iS i0)))) (var i0)) (var i0 ::s split (force (var (iS (iS i0)))) (var (iS i0))))))

  {- merge (l1 l2 : list nat) : list nat =
       match l1 with
       [] -> l2
       x :: xs ->
         match l2 with
           [] -> x :: xs
           y :: ys ->
             x <= y -> x :: merge xs l2
             _ -> y :: merge l1 ys -}
  merge : ∀ {Γ} → Γ Source.|- ((list nat ×s list nat) ->s list nat)
  merge = lam (listrec (split (var i0) (var i0))
            (split (var i0) (var (iS i0)))
            (listrec (split (var (iS (iS (iS i0)))) (var (iS i0)))
              (split (var (iS (iS (iS i0)))) (var i0))
              (rec (app (app leq (var (iS (iS (iS i0))))) (var i0))
                (var (iS (iS (iS i0))) ::s force (var (iS (iS (iS (iS (iS i0)))))))
                (var i0 ::s app merge (prod (split (var (iS (iS (iS (iS (iS (iS (iS (iS i0))))))))) (var (iS i0))) (var (iS (iS (iS i0))))))))) 

  {- mergesort (l : list nat) : list nat -}
  msort : ∀ {Γ} → Γ Source.|- (list nat ->s list nat)
  msort = lam (listrec (var i0)
            nil
            (listrec (var (iS i0))
              (var i0 ::s nil)
              (app merge (prod
                (app msort (split (app halve (var (iS (iS (iS (iS (iS (iS i0)))))))) (var i0)))
                (app msort (split (app halve (var (iS (iS (iS (iS (iS (iS i0)))))))) (var (iS i0))))))))

open import Preliminaries

module Focusing where

  data Tp : Set where
    b : Tp
    _⇒'_ : Tp → Tp → Tp
    _×'_ : Tp → Tp → Tp

  Ctx = List Tp

  data _∈_ : Tp → Ctx → Set where
    i0 : ∀ {Γ τ} → τ ∈ τ :: Γ
    iS : ∀ {Γ τ τ1} → τ ∈ Γ → τ ∈ τ1 :: Γ

  -- datatype of focused proofs for negative fragment of intuitionistic logic
  data _,,_|-_ : Ctx → Maybe Tp → Tp → Set where

  -- focus and init

    focus : ∀ {Γ A P} →

          A ∈ Γ → Γ ,, (Some A) |- P
          -------------------------- focus
          → Γ ,, None |- P

    init : ∀ {Γ P} →

         ------------------ init
         Γ ,, (Some P) |- P

  -- synchronous rules

    arr-l : ∀ {Γ A B P} →

          Γ ,, None |- A → Γ ,, (Some B) |- P
          ----------------------------------- impl-left
          → Γ ,, (Some (A ⇒' B)) |- P

    conj-l1 : ∀ {Γ A B P} →

            Γ ,, (Some A) |- P
            --------------------------- conj-left1
            → Γ ,, (Some (A ×' B)) |- P
    conj-l2 : ∀ {Γ A B P} →

            Γ ,, (Some B) |- P
            --------------------------- conj-left2 
            → Γ ,, (Some (A ×' B)) |- P

  -- asynchronous rules

    arr-r : ∀ {Γ A B} →

          (A :: Γ) ,, None |- B
          ----------------------- impl-right
          → Γ ,, None |- (A ⇒' B)

    conj-r : ∀ {Γ A B} →

           Γ ,, None |- A → Γ ,, None |- B
           ------------------------------- conj-right
           → Γ ,, None |- (A ×' B)

  -- examples

  i : ∀ {A} → [] ,, None |- (A ⇒' A)
  i = arr-r (focus i0 init)

  #2 : ∀ {A B} → [] ,, None |- (A ⇒' (B ⇒' B))
  #2 = arr-r (arr-r (focus i0 init))

  k : ∀ {A B} → [] ,, None |- (A ⇒' (B ⇒' A))
  k = arr-r (arr-r (focus (iS i0) init))

  s : ∀ {A B C} → [] ,, None |- ((A ⇒' (B ⇒' C)) ⇒' ((A ⇒' B) ⇒' (A ⇒' C)))
  s = arr-r (arr-r (arr-r (focus (iS (iS i0)) (arr-l (focus i0 init) (arr-l (focus (iS i0) (arr-l (focus i0 init) init)) init)))))

  #5 : ∀ {A B} → [] ,, None |- (A ⇒' (B ⇒' (A ×' B)))
  #5 = arr-r (arr-r (conj-r (focus (iS i0) init) (focus i0 init)))

  #6 : ∀ {A B} → [] ,, None |- (A ⇒' (A ×' (B ⇒' B)))
  #6 = arr-r (conj-r (focus i0 init) (arr-r (focus i0 init)))

  mp : ∀ {A B} → [] ,, None |- ((A ×' (A ⇒' B)) ⇒' B)
  mp = arr-r (focus i0 (conj-l2 (arr-l (focus i0 (conj-l1 init)) init)))


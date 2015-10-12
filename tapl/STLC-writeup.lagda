\documentclass[11pt]{article}

\def\textmu{}

%include agda.fmt
\usepackage{textgreek} % not reproducible without textgreek

\usepackage{mathtools}
\usepackage{verbatim}
\usepackage{bussproofs}
\usepackage{hyperref}

\usepackage{fullpage}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{amssymb}
\usepackage{enumerate}
\usepackage{wasysym}

\newtheorem*{defn}{Definition}
\newtheorem*{claim}{Claim}
\newtheorem*{lemma}{Lemma}
\newtheorem*{base}{Base case}

\pagestyle{empty}

\begin{document}

\title{A Formalized Proof of Strong Normalization for the\\Simply-Typed $\lambda$-Calculus in Agda}
\author{Ben Hudson}
\maketitle

\section{Introduction}

We present a formalized proof of strong normalization for the simply-typed $\lambda$-calculus in Agda, a dependently-typed programming language and proof assistant.  Our approach is inspired by the Edward Yang’s Agda proof of weak normalization for STLC (\url{https://github.com/ezyang/lr-agda/blob/master/STLC-CBN.agda}), which in turn was an exercise from Dan Licata’s `Dependently-Typed Programming in Agda’ course at OPLSS 2013.

\section{Formalization of STLC}

The types of the simply-typed $\lambda$-calculus can be defined in Agda as an inductive datatype:

\begin{code}
data Tp : Set where
    b : Tp
    _⇒_ : Tp → Tp → Tp
\end{code}

where $b$ is some uninterpreted base type.  Contexts $\Gamma$ are lists of types, indexed by de Bruijn indices:

\begin{code}
  Ctx = List Tp

  data _∈_ : Tp → List Tp → Set where
    i0 : ∀ {Γ τ} → τ ∈ (τ :: Γ)
    iS : ∀ {Γ τ τ1} → τ ∈ Γ → τ ∈ (τ1 :: Γ)
\end{code}

Typing judgements are of the form $\Gamma$ $\vdash$ $\tau$ (read: ``$\Gamma$ proves $\tau$,'' or ``$\tau$ is derivable from the rules in $\Gamma$'').  We can represent typing judgements and closed values of the STLC as follows:

\begin{code}
data _|-_ : Ctx → Tp → Set where
  c   : ∀ {Γ} → Γ |- b
  v   : ∀ {Γ τ} 
      → τ ∈ Γ
      → Γ |- τ
  lam : ∀ {Γ τ1 τ2} → (τ1 :: Γ) |- τ2 → Γ |- τ1 ⇒ τ2
  app : ∀ {Γ τ1 τ2} → Γ |- τ1 ⇒ τ2 → Γ |- τ1 → Γ |- τ2

data val :  {τ : Tp} → [] |- τ → Set where
  c-isval : val c
  lam-isval : {τ₁ τ₂ : Tp} {e : τ₁ :: [] |- τ₂} → val (lam e)
\end{code}

The $val$ declaration simply says that the only values in the STLC are constants of the base type, and $\lambda$-abstractions.  For our proof, we use call-by-name small-step operational semantics:

\begin{code}
data _↦_ : {τ : Tp} → [] |- τ → [] |- τ → Set where
  Step/app : {τ1 τ2 : Tp} {e1 e1' : [] |- τ1 ⇒ τ2} {e2 : [] |- τ1}
           → e1 ↦ e1'
           → app e1 e2 ↦ app e1' e2
  Step/β : {τ1 τ2 : Tp} {e : τ1 :: [] |- τ2} {e1 : [] |- τ1}
         → app (lam e) e1 ↦ subst1 e1 e

  data _↦*_ : {τ : Tp} → [] |- τ → [] |- τ → Set where
    Done : {τ : Tp} {e : [] |- τ} → e ↦* e
    Step : {τ : Tp} {e1 e2 e3 : [] |- τ} 
         → e1 ↦ e2  →  e2 ↦* e3
         → e1 ↦* e3
\end{code}


where $\mapsto*$ is the reflexive/transitive closure of the step relation $\mapsto$.

\section{Strong Normalization}

Strong normalization states that all well-typed terms evaluate to a normal form, i.e. ``if $e$ is a well-typed term, then $e \Downarrow$,’’ where we can formalize evaluation to a normal form as:

\begin{code}
_⇓ : {τ : Tp} → [] |- τ → Set
e ⇓ = Σ (λ k → e ⇓ k)
\end{code}

where $\Downarrow$ is defined as

\begin{code}
_⇓_ : {τ : Tp} → [] |- τ → [] |- τ → Set
e ⇓ k = val k × e ↦* k
\end{code}

Intuitively, this says ``$e$ is strongly normalizing if there is some $k$ such that $k$ is a value and there is a reduction sequence from $e$ to $k$’’.

A first attempt at proving strong normalization would usually be done by first inducting on the structure of the term $e$.  However, when we arrive at the case where we want to show strong normalization for an application $e1\ e2$, we get stuck, because we don’t know if substitution during $\beta$-reduction normalizes.

To overcome this problem, we define a unary logical relation $SN_\tau$ by induction on type $\tau$:

\begin{code}
SN : (τ : Tp) → [] |- τ → Set
SN b e = e ⇓
SN (t1 ⇒ t2) e = e ⇓ × Σ (λ e' → SN t1 e' → SN t2 (app e e'))
\end{code}

A unary logical relation is just a logical predicate: $SN_b(e)$ means an expression of base type $b$ holds for $SN$ iff $e \Downarrow$.  The case for function of type $\tau1\to\tau2$ states that $SN_{(t1\to t2)}(e)$ iff $e \Downarrow$, and for all e', $SN_{t1}(e’)$ implies $SN_{t2}(e\ e’)$.  This condition allows us to show that the logical relation is preserved by the elimination form for function types (application).

We also need to ensure substitutions are strongly normalizing:

\begin{code}
SNc : (Γ : Ctx) → sctx [] Γ → Set
SNc [] Θ = Unit
SNc (τ :: Γ) Θ = SNc Γ (throw Θ) × SN τ (Θ i0)
\end{code}

This leads us to the fundamental theorem of logical relations that we would like to prove:

\begin{code}
fund : {Γ : Ctx} {τ : Tp} {Θ : sctx [] Γ} 
     → (e : Γ |- τ)
     → SNc Γ Θ
     → SN τ (subst e Θ)
\end{code}

This says that all well-typed terms $e : \tau$ hold for the logical relation $SN_\tau$ which we have just defined.

\end{document}
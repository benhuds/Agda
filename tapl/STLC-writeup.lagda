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

We present a formalized proof of strong normalization for the simply-typed $\lambda$-calculus in Agda, a dependently-typed programming language and proof assistant.  Our approach is inspired by the Edward Yang’s Agda proof of weak normalization for STLC (\url{https://github.com/ezyang/lr-agda/blob/master/STLC-CBN.agda}), which in turn was an exercise from Dan Licata’s `Dependently-Typed Programming in Agda’ course at OPLSS 2013.  Our approach is also inspired by Amal Ahmed’s lecture slides on logical relations from OPLSS 2013 (\url{https://www.cs.uoregon.edu/research/summerschool/summer13/lectures/ahmed-1.pdf}).

\section{Formalization of STLC}

The types of the simply-typed $\lambda$-calculus can be defined in Agda as an inductive datatype:

\begin{code}
data Tp : Set where
    b : Tp
    _⇒_ : Tp → Tp → Tp
     nat : Typ
    _?_ : Typ ? Typ ? Typ
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
_⇓_ : {τ : Tp} → [] |- τ → [] |- τ → Set
e ⇓ k = val k × e ↦* k
\end{code}

The statement of strong normalization can then be stated as follows:

\begin{code}
_⇓ : {τ : Tp} → [] |- τ → Set
e ⇓ = Σ (λ k → e ⇓ k)
\end{code}

Intuitively, this says ``$e$ is strongly normalizing if there is some $k$ such that $k$ is a value and there is a reduction sequence from $e$ to $k$’’.

A first attempt at proving strong normalization would usually be done by first inducting on the structure of the term $e$.  However, when we arrive at the case where we want to show strong normalization for an application $e1\ e2$, we get stuck, because we don’t know if substitution during $\beta$-reduction normalizes.

To overcome this problem, we define a unary logical relation $SN_\tau$ by induction on type $\tau$:

\begin{code}
SN : (τ : Tp) → [] |- τ → Set
SN b e = e ⇓
SN (t1 ⇒ t2) e = e ⇓ × Σ (λ e' → SN t1 e' → SN t2 (app e e'))
\end{code}

A unary logical relation is just a logical predicate: $SN_b(e)$ means an expression $e$ of base type $b$ holds for $SN$ iff $e \Downarrow$.  The case for function of type $\tau1\to\tau2$ states that $SN_{(t1\to t2)}(e)$ iff $e \Downarrow$, and for all e', $SN_{t1}(e’)$ implies $SN_{t2}(e\ e’)$.  This condition allows us to show that the logical relation is preserved by the elimination form for function types (application).

We also need to ensure substitutions are strongly normalizing:

\begin{code}
SNc : (Γ : Ctx) → sctx [] Γ → Set
SNc [] Θ = Unit
SNc (τ :: Γ) Θ = SNc Γ (throw Θ) × SN τ (Θ i0)
\end{code}

This leads us to the fundamental lemma that we would like to prove:

\begin{lemma}[Fundamental lemma]
If $e : \Gamma \vdash \tau$ and substitutions $\Theta$ on contexts $\Gamma$ preserve $SN_\tau$, then $SN_\tau(\Theta\ e)$.
\end{lemma}

\begin{proof}
We begin by stating the lemma in Agda:

\begin{code}
fund : {Γ : Ctx} {τ : Tp} {Θ : sctx [] Γ} 
     → (e : Γ |- τ)
     → SNc Γ Θ
     → SN τ (subst e Θ)
fund e snc = ?
\end{code}

\begin{comment}This says that all well-typed terms $e : \tau$ hold for the logical relation $SN_\tau$ which we have just defined.
\end{comment}
We proceed by pattern matching on $e$, which corresponds to term induction on $e$:

\begin{code}
fund c snc = ? c , (c-isval , Done)
fund (v x) snc = ? fund (v x) (fst snc)
fund (lam e) snc = ?
fund (app e1 e2) snc = ?
\end{code}

The formalized proof proceeds in a similar fashion to a traditional proof on paper:

Case: $e$ is a constant $c$ of the base type $b$.  By definition, $SN_b(\Theta(c))$ iff $\Theta(c) \Downarrow$.  However, we know that $\Theta(c) = c$, so all we are really showing in this case is $c \Downarrow$, i.e. there is a $v$ such that $v$ is a value and $c \mapsto*v$.  If we let $v$ be the $c$ itself, the result follows trivially - we know all constants of the base type are values (\texttt{c-isval}), and $e \mapsto*e$ for all $e : \Gamma\vdash\tau$ (\texttt{Done}).  We can fill in the proof in Agda as follows:

\begin{code}
fund c snc = c , (c-isval , Done)
\end{code}

Case: $e$ is a variable $x$ in the context $\Gamma$.  We want to show $SN_\tau(\Theta(x))$, where $\Theta$ maps variables to closed values.  Since $\Theta$ maps variables to closed values, we know $\Theta(x) = v$, where $v$ is some closed value, but $SN_\tau(v)$ by definition, so this case holds trivially.

Case: $e$ is an abstraction $\lambda x.e$.  We want to show $SN_{\tau1\to\tau2}(\Theta(\lambda x.e))$.

Case: $e$ is an application $e1\ e2$, where $e1$ and $e2$ are terms.  We want to show $SN_{\tau2}(\Theta(e1\ e2))$.  By IH, we know $SN_{\tau1\to\tau2}(\Theta(e1))$ and $SN_{\tau1}(\Theta(e2))$.  We know that the IH on $e1$, $SN_{\tau1\to\tau2}(\Theta(e1))$, iff $e1 \Downarrow$ and for all $e’$ such that $SN_{\tau1}e’$, we can conclude $SN_{\tau1}((\Theta\ e)\ e’)$.  However, we know by the IH on $e2$ that $SN_{\tau1}(\Theta(e2))$, so we can apply this to the IH on $e1$ to obtain our result.

\end{proof}

\end{document}
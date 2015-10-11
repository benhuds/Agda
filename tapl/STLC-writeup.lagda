\documentclass[11pt]{article}

\def\textmu{}

%include agda.fmt
\usepackage{textgreek} % not reproducible without textgreek

\usepackage{mathtools}
\usepackage{verbatim}
\usepackage{bussproofs}

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

We present a formalized proof of strong normalization for the simply-typed $\lambda$-calculus in Agda, a dependently-typed programming language and proof assistant.

\section{Formalization of STLC}

The syntax of the simply-typed $\lambda$-calculus can be formalized as follows:

\begin{code}
data Tp : Set where
    b : Tp
    _⇒_ : Tp → Tp → Tp
\end{code}

where $b$ is some uninterpreted base type.

\begin{code}
  data _|-_ : Ctx → Tp → Set where
    c   : ∀ {Γ} → Γ |- b -- some constant of the base type
    v   : ∀ {Γ τ} 
        → τ ∈ Γ
        → Γ |- τ
    lam : ∀ {Γ τ1 τ2} → (τ1 :: Γ) |- τ2 → Γ |- τ1 ⇒ τ2
    app : ∀ {Γ τ1 τ2} → Γ |- τ1 ⇒ τ2 → Γ |- τ1 → Γ |- τ2

  data val :  {τ : Tp} → [] |- τ → Set where
    c-isval : val c
    lam-isval : {τ₁ τ₂ : Tp} {e : τ₁ :: [] |- τ₂} → val (lam e)
\end{code}

\section{Strong Normalization}

\end{document}
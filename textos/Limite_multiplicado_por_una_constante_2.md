---
title: Si el límite de la sucesión u(n) es a y c ∈ ℝ, entonces el límite de u(n)c es ac
date: 2024-11-29 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

En Lean, una sucesión \(u\_0, u\_1, u\_2, ...\) se puede representar mediante una función \(u : ℕ → ℝ\) de forma que \(u(n)\) es \u\_n\).

Se define que \(a\) es el límite de la sucesión \(u\), por
<pre lang="lean">
   def limite : (ℕ → ℝ) → ℝ → Prop :=
     fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
</pre>

Demostrar que que si el límite de \(u\_n) es \(a\), entonces el de \(u\_n c\) es \(ac\).

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u : ℕ → ℝ)
variable (a c : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (h : limite u a)
  : limite (fun n ↦ (u n) * c) (a * c) :=
by sorry
</pre>
<!--more-->

<h2>1. Proof in natural language</h2>



<h2>2. Proofs with Lean4</h2>

<pre lang="lean">
</pre>

You can interact with the previous proofs at [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/???).

<h2>3. Proofs with Isabelle/HOL</h2>

<pre lang="isar">
</pre>

------------------------------------------------------------------------

**Note:** The code for the previous proofs can be found in the [Calculemus repository](https://github.com/jaalonso/Calculemus2) on GitHub.

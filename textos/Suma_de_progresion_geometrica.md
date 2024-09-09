---
title: Pruebas de a+aq+aq²+···+aqⁿ = a(1-qⁿ⁺¹)/(1-q)
date: 2024-09-09 06:00:00 UTC+02:00
category: Inducción
has_math: true
---

[mathjax]

Demostrar que si \\(q ≠ 1\\), entonces la suma de los términos de la progresión geométrica
\\[ a + aq + aq^2 + ··· + aq^n \\]
es
\\[ \\dfrac{a(1 - q^{n+1})}{1 - q} \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a q : ℝ)

def sumaPG : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, q, n + 1 => sumaPG a q n + (a * q^(n + 1))

example
  (h : q ≠ 1)
  : sumaPG a q n = a * (1 - q^(n + 1)) / (1 - q) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea
\\[ s(a,q,n) = a + aq + aq^2 + ··· + aq^n \\]
Tenemos que demostrar que
\\[ s(a,q,n) = a(1 - q^{n+1})/(1 - q) \\]
o, equivalentemente que
\\[ (1 - q)s(a,q,n) = a(1 - q^{n+1}) \\]
Lo haremos por inducción sobre \\(n\\).

**Caso base:** Sea \\(n = 0\\). Entonces,
\\begin{align}
   (1 - q)s(a,q,n) &= (1 - q)s(a, q, 0) \\\\
                   &= (1 - q)a          \\\\
                   &= a(1 - q^{0 + 1})  \\\\
                   &= a(1 - q^{n + 1})
\\end{align}

**Paso de inducción:** Sea \\(n = m+1\\) y supongamos la hipótesis de inducción (HI)
\\[ (1 - q)s(a,q,m) = a(1 - q^{n + 1}) \\]
Entonces,
\\begin{align}
   (1 - q)s(a,q,n)                           \\\\
   &= (1 - q)s(a,q,m+1)                      \\\\
   &= (1 - q)(s(a,q,m) + aq^(m + 1))         \\\\
   &= (1 - q)s(a,q,m) + (1 - q)aq^(m + 1)    \\\\
   &= a(1 - q^(m + 1)) + (1 - q)aq^(m + 1)   &&\\text{[por HI]} \\\\
   &= a(1 - q^(m + 1 + 1))                   \\\\
   &= a(1 - q^(n + 1))
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a q : ℝ)

set_option pp.fieldNotation false

@[simp]
def sumaPG : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, q, n + 1 => sumaPG a q n + (a * q^(n + 1))

-- 1ª demostración
-- ===============

example
  (h : q ≠ 1)
  : sumaPG a q n = a * (1 - q^(n + 1)) / (1 - q) :=
by
  have h1 : 1 - q ≠ 0 := by exact sub_ne_zero_of_ne (id (Ne.symm h))
  suffices h : (1 - q) * sumaPG a q n = a * (1 - q ^ (n + 1))
    from by exact CancelDenoms.cancel_factors_eq_div h h1
  induction n with
  | zero =>
    -- ⊢ (1 - q) * sumaPG a q 0 = a * (1 - q ^ (0 + 1))
    calc (1 - q) * sumaPG a q 0
         = (1 - q) * a           := by simp only [sumaPG]
       _ = a * (1 - q)           := by simp only [mul_comm]
       _ = a * (1 - q ^ 1)       := by simp
       _ = a * (1 - q ^ (0 + 1)) := by simp
  | succ m HI =>
    -- m : ℕ
    -- HI : (1 - q) * sumaPG a q m = a * (1 - q ^ (m + 1))
    -- ⊢ (1 - q) * sumaPG a q (m + 1) = a * (1 - q ^ (m + 1 + 1))
    calc (1 - q) * sumaPG a q (m + 1)
         = (1 - q) * (sumaPG a q m + (a * q^(m + 1)))
           := by simp only [sumaPG]
       _ = (1 - q) * sumaPG a q m + (1 - q) * (a * q ^ (m + 1))
           := by rw [left_distrib]
       _ = a * (1 - q ^ (m + 1)) + (1 - q) * (a * q ^ (m + 1))
           := congrArg  (. + (1 - q) * (a * q ^ (m + 1))) HI
       _ = a * (1 - q ^ (m + 1 + 1))
           := by ring_nf

-- 2ª demostración
-- ===============

example
  (h : q ≠ 1)
  : sumaPG a q n = a * (1 - q^(n + 1)) / (1 - q) :=
by
  have h1 : 1 - q ≠ 0 := by exact sub_ne_zero_of_ne (id (Ne.symm h))
  suffices h : (1 - q) * sumaPG a q n = a * (1 - q ^ (n + 1))
    from by exact CancelDenoms.cancel_factors_eq_div h h1
  induction n with
  | zero =>
    -- ⊢ (1 - q) * sumaPG a q 0 = a * (1 - q ^ (0 + 1))
    simp
    -- ⊢ (1 - q) * a = a * (1 - q)
    ring_nf
  | succ m HI =>
    -- m : ℕ
    -- HI : (1 - q) * sumaPG a q m = a * (1 - q ^ (m + 1))
    -- ⊢ (1 - q) * sumaPG a q (m + 1) = a * (1 - q ^ (m + 1 + 1))
    calc (1 - q) * sumaPG a q (m + 1)
         = (1 - q) * (sumaPG a q m + (a * q ^ (m + 1)))
           := rfl
       _ = (1 - q) * sumaPG a q m + (1 - q) * (a * q ^ (m + 1))
           := by ring_nf
       _ = a * (1 - q ^ (m + 1)) + (1 - q) * (a * q ^ (m + 1))
           := congrArg  (. + (1 - q) * (a * q ^ (m + 1))) HI
       _ = a * (1 - q ^ (m + 1 + 1))
           := by ring_nf
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Suma_de_progresion_geometrica.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Suma_de_progresion_geometrica
imports Main HOL.Real
begin

fun sumaPG :: "real ⇒ real ⇒ nat ⇒ real" where
  "sumaPG a q 0 = a"
| "sumaPG a q (Suc n) = sumaPG a q n + (a * q^(n + 1))"

(* 1ª demostración *)
lemma
  "(1 - q) * sumaPG a q n = a * (1 - q^(n + 1))"
proof (induct n)
  show "(1 - q) * sumaPG a q 0 = a * (1 - q ^ (0 + 1))"
    by simp
next
  fix n
  assume HI : "(1 - q) * sumaPG a q n = a * (1 - q ^ (n + 1))"
  have "(1 - q) * sumaPG a q (Suc n) =
        (1 - q) * (sumaPG a q n + (a * q^(n + 1)))"
    by simp
  also have "… = (1 - q) * sumaPG a q n + (1 - q) * a * q^(n + 1)"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q ^ (n + 1)) + (1 - q) * a * q^(n + 1)"
    using HI by simp
  also have "… = a * (1 - q ^ (n + 1) + (1 - q) * q^(n + 1))"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q ^ (n + 1) +  q^(n + 1) - q^(n + 2))"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q^(n + 2))"
    by simp
  also have "… = a * (1 - q ^ (Suc n + 1))"
    by simp
  finally show "(1 - q) * sumaPG a q (Suc n) = a * (1 - q ^ (Suc n + 1))"
    by this
qed

(* 2ª demostración *)
lemma
  "(1 - q) * sumaPG a q n = a * (1 - q^(n + 1))"
proof (induct n)
  show "(1 - q) * sumaPG a q 0 = a * (1 - q ^ (0 + 1))"
    by simp
next
  fix n
  assume HI : "(1 - q) * sumaPG a q n = a * (1 - q ^ (n + 1))"
  have "(1 - q) * sumaPG a q (Suc n) =
        (1 - q) * sumaPG a q n + (1 - q) * a * q^(n + 1)"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q ^ (n + 1)) + (1 - q) * a * q^(n + 1)"
    using HI by simp
  also have "… = a * (1 - q ^ (n + 1) +  q^(n + 1) - q^(n + 2))"
    by (simp add: algebra_simps)
  finally show "(1 - q) * sumaPG a q (Suc n) = a * (1 - q ^ (Suc n + 1))"
    by simp
qed

(* 3ª demostración *)
lemma
  "(1 - q) * sumaPG a q n = a * (1 - q^(n + 1))"
  using power_add
  by (induct n) (auto simp: algebra_simps)

end
</pre>

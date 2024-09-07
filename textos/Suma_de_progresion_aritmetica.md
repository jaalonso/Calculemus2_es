---
title: Pruebas de a+(a+d)+(a+2d)+···+(a+nd)=(n+1)(2a+nd)/2
date: 2024-09-07 06:00:00 UTC+02:00
category: Inducción
has_math: true
---

[mathjax]

Demostrar que la suma de los términos de la progresión aritmética
\\[ a + (a + d) + (a + 2d) + ··· + (a + nd) \\]
es
[ \\dfrac{(n + 1)(2a + n d)}{2} \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a d : ℝ)

def sumaPA : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, d, n + 1 => sumaPA a d n + (a + (n + 1) * d)

example :
  2 * sumaPA a d n = (n + 1) * (2 * a + n * d) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea
\\[ s(a,d,n) = a + (a + d) + (a + 2d) + ··· + (a + nd) \\]
Tenemos que demostrar que
\\[ s(a,d,n) = \\dfrac{(n + 1)(2a + nd)}{2} \\]
o, equivalentemente que
\\[ 2s(a,d,n) = (n + 1)(2a + nd) \\]
Lo haremos por inducción sobre \\(n\\).

**Caso base:** Sea \\(n = 0\\). Entonces,
\\begi{align}
   2s(a,d,n) &= 2s(a,d,0)         \\\\
             &= 2·a               \\\\
             &= (0 + 1)(2a + 0.d) \\\\
             &= (n + 1)(2a + nd)
\\end{align}

**Paso de indución:** Sea \\(n = m+1\\) y supongamos la hipótesis de inducción (HI)
\\[ 2s(m) = (m + 1)(2a + md) \\]
Entonces,
\\begin{align}
   2s(n) &= 2s(m+1)                              \\\\
         &= 2(s(a,d,m) + (a + (m + 1)d))         \\\\
         &= 2s(a,d,m) + 2(a + (m + 1)d)          \\\\
         &= ((m + 1)(2a + md)) + 2(a + (m + 1)d) &&\\text{[por HI]} \\\\
         &= (m + 2)(2a + (m + 1)d)               \\\\
         &= (n + 1)(2a + nd)
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a d : ℝ)

set_option pp.fieldNotation false

def sumaPA : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, d, n + 1 => sumaPA a d n + (a + (n + 1) * d)

@[simp]
lemma sumaPA_zero :
  sumaPA a d 0 = a :=
by simp only [sumaPA]

@[simp]
lemma sumaPA_succ :
  sumaPA a d (n + 1) = sumaPA a d n + (a + (n + 1) * d) :=
by simp only [sumaPA]

-- 1ª demostración
-- ===============

example :
  2 * sumaPA a d n = (n + 1) * (2 * a + n * d) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sumaPA a d 0 = (↑0 + 1) * (2 * a + ↑0 * d)
    have h : 2 * sumaPA a d 0 = (0 + 1) * (2 * a + 0 * d) :=
      calc 2 * sumaPA a d 0
           = 2 * a
               := congrArg (2 * .) (sumaPA_zero a d)
         _ = (0 + 1) * (2 * a + 0 * d)
               := by ring_nf
    exact_mod_cast h
  | succ m HI =>
    -- m : ℕ
    -- HI : 2 * sumaPA a d m = (↑m + 1) * (2 * a + ↑m * d)
    -- ⊢ 2 * sumaPA a d (m + 1) = (↑(m + 1) + 1) * (2 * a + ↑(m + 1) * d)
    calc 2 * sumaPA a d (succ m)
         = 2 * (sumaPA a d m + (a + (m + 1) * d))
           := congrArg (2 * .) (sumaPA_succ m a d)
       _ = 2 * sumaPA a d m + 2 * (a + (m + 1) * d)
           := by ring_nf
       _ = ((m + 1) * (2 * a + m * d)) + 2 * (a + (m + 1) * d)
           := congrArg (. + 2 * (a + (m + 1) * d)) HI
       _ = (m + 2) * (2 * a + (m + 1) * d)
           := by ring_nf
       _ = (succ m + 1) * (2 * a + succ m * d)
           := by norm_cast

-- 2ª demostración
-- ===============

example :
  2 * sumaPA a d n = (n + 1) * (2 * a + n * d) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sumaPA a d 0 = (↑0 + 1) * (2 * a + ↑0 * d)
    simp
  | succ m HI =>
    -- m : ℕ
    -- HI : 2 * sumaPA a d m = (↑m + 1) * (2 * a + ↑m * d)
    -- ⊢ 2 * sumaPA a d (m + 1) = (↑(m + 1) + 1) * (2 * a + ↑(m + 1) * d)
    calc 2 * sumaPA a d (succ m)
         = 2 * (sumaPA a d m + (a + (m + 1) * d))
           := rfl
       _ = 2 * sumaPA a d m + 2 * (a + (m + 1) * d)
           := by ring_nf
       _ = ((m + 1) * (2 * a + m * d)) + 2 * (a + (m + 1) * d)
           := congrArg (. + 2 * (a + (m + 1) * d)) HI
       _ = (m + 2) * (2 * a + (m + 1) * d)
           := by ring_nf
       _ = (succ m + 1) * (2 * a + succ m * d)
           := by norm_cast
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Suma_de_progresion_aritmetica.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Suma_de_progresion_aritmetica
imports Main HOL.Real
begin

fun sumaPA :: "real ⇒ real ⇒ nat ⇒ real" where
  "sumaPA a d 0 = a"
| "sumaPA a d (Suc n) = sumaPA a d n + (a + (n + 1) * d)"

(* 1ª demostración *)
lemma
  "2 * sumaPA a d n = (n + 1) * (2 * a + n * d)"
proof (induct n)
  show "2 * sumaPA a d 0 =
        (real 0 + 1) * (2 * a + real 0 * d)"
    by simp
next
  fix n
  assume HI : "2 * sumaPA a d n =
               (n + 1) * (2 * a + n * d)"
  have "2 * sumaPA a d (Suc n) =
        2 * (sumaPA a d n + (a + (n + 1) * d))"
    by simp
  also have "… = 2 * sumaPA a d n + 2 * (a + (n + 1) * d)"
    by simp
  also have "… = (n + 1) * (2 * a + n * d) + 2 * (a + (n + 1) * d)"
    using HI by simp
  also have "… = (real (Suc n) + 1) * (2 * a + (Suc n) * d)"
    by (simp add: algebra_simps)
  finally show "2 * sumaPA a d (Suc n) =
                (real (Suc n) + 1) * (2 * a + (Suc n) * d)"
    by this
qed

(* 2ª demostración *)
lemma
  "2 * sumaPA a d n = (n + 1) * (2*a + n*d)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: algebra_simps)
qed

(* 3ª demostración *)
lemma
  "2 * sumaPA a d n = (n + 1) * (2*a + n*d)"
by (induct n) (simp_all add: algebra_simps)

end
</pre>

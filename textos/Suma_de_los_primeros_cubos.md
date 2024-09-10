---
title: Pruebas de 0³+1³+2³+3³+···+n³ = (n(n+1)/2)²
date: 2024-09-10 06:00:00 UTC+02:00
category: Inducción
has_math: true
---

[mathjax]

Demostrar que la suma de los primeros cubos
\\[ 0^3 + 1^3 + 2^3 + 3^3 + ··· + n^3 \\]
es
\\[ \\dfrac{n(n+1)}{2}^2 \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)

def sumaCubos : ℕ → ℕ
  | 0   => 0
  | n+1 => sumaCubos n + (n+1)^3

example :
  4 * sumaCubos n = (n*(n+1))^2 :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea
\\[ s(n) = 0^3 + 1^3 + 2^3 + 3^3 + ··· + n^3 \\]
Tenemos que demostrar que
\\[ s(n) = \\dfrac{n(n+1)}{2}^2 \\]
o, equivalentemente que
\\[ 4s(n) = (n(n+1))^2 \\]
Lo haremos por inducción sobre n.

**Caso base:** Sea \\(n = 0\\). Entonces,
\\begin{align}
   4s(n) &= 4s(0)        \\\\
         &= 4·0          \\\\
         &= 0            \\\\
         &= (0(0 + 1))^2 \\\\
         &= (n(n + 1))^2
\\end{align}

**Paso de inducción:** Sea \\(n = m+1\\) y supongamos la hipótesis de inducción (HI)
\\[ 4s(m) = (m(m + 1))^2 \\]
Entonces,
\\begin{align}
   4s(n) &= 4s(m+1)                       \\\\
         &= 4(s(m) + (m+1)^3)             \\\\
         &= 4s(m) + 4(m+1)^3              \\\\
         &= (m*(m+1))^2 + 4(m+1)^3        [por HI]
         &= (m+1)^2*(m^2+4m+4)            \\\\
         &= (m+1)^2*(m+2)^2               \\\\
         &= ((m+1)(m+2))^2                \\\\
         &= ((m+1)(m+1+1))^2
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)

set_option pp.fieldNotation false

@[simp]
def sumaCubos : ℕ → ℕ
  | 0   => 0
  | n+1 => sumaCubos n + (n+1)^3

-- 1ª demostración
-- ===============

example :
  4 * sumaCubos n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    -- ⊢ 4 * sumaCubos 0 = (0 * (0 + 1)) ^ 2
    calc 4 * sumaCubos 0
         = 4 * 0             := by simp only [sumaCubos]
       _ = (0 * (0 + 1)) ^ 2 := by simp
  | succ m HI =>
     -- m : ℕ
     -- HI : 4 * sumaCubos m = (m * (m + 1)) ^ 2
     -- ⊢ 4 * sumaCubos (m + 1) = ((m + 1) * (m + 1 + 1)) ^ 2
    calc 4 * sumaCubos (m + 1)
         = 4 * (sumaCubos m + (m+1)^3)
           := by simp only [sumaCubos]
       _ = 4 * sumaCubos m + 4*(m+1)^3
           := by ring
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) HI
       _ = (m+1)^2*(m^2+4*m+4)
           := by ring
       _ = (m+1)^2*(m+2)^2
           := by ring
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1))^2
           := by simp

-- 2ª demostración
-- ===============

example :
  4 * sumaCubos n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    simp
  | succ m HI =>
    calc 4 * sumaCubos (m+1)
         = 4 * sumaCubos m + 4*(m+1)^3
           := by {simp ; ring_nf}
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) HI
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1)) ^ 2
           := by simp
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Suma_de_los_primeros_cubos.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Suma_de_los_primeros_cubos
imports Main
begin

fun sumaCubos :: "nat ⇒ nat" where
  "sumaCubos 0       = 0"
| "sumaCubos (Suc n) = sumaCubos n + (Suc n)^3"

(* 1ª demostración *)
lemma
  "4 * sumaCubos n = (n*(n+1))^2"
proof (induct n)
  show "4 * sumaCubos 0 = (0 * (0 + 1))^2"
    by simp
next
  fix n
  assume HI : "4 * sumaCubos n = (n * (n + 1))^2"
  have "4 * sumaCubos (Suc n) = 4 * (sumaCubos n + (n+1)^3)"
    by simp
  also have "… = 4 * sumaCubos n + 4*(n+1)^3"
    by simp
  also have "… = (n*(n+1))^2 + 4*(n+1)^3"
    using HI by simp
  also have "… = (n+1)^2*(n^2+4*n+4)"
    by algebra
  also have "… = (n+1)^2*(n+2)^2"
    by algebra
  also have "… = ((n+1)*((n+1)+1))^2"
    by algebra
  also have "… = (Suc n * (Suc n + 1))^2"
    by (simp only: Suc_eq_plus1)
  finally show "4 * sumaCubos (Suc n) = (Suc n * (Suc n + 1))^2"
    by this
qed

(* 2ª demostración *)
lemma
  "4 * sumaCubos n = (n*(n+1))^2"
proof (induct n)
  show "4 * sumaCubos 0 = (0 * (0 + 1))^2"
    by simp
next
  fix n
  assume HI : "4 * sumaCubos n = (n * (n + 1))^2"
  have "4 * sumaCubos (Suc n) = 4 * sumaCubos n + 4*(n+1)^3"
    by simp
  also have "… = (n*(n+1))^2 + 4*(n+1)^3"
    using HI by simp
  also have "… = ((n+1)*((n+1)+1))^2"
    by algebra
  also have "… = (Suc n * (Suc n + 1))^2"
    by (simp only: Suc_eq_plus1)
  finally show "4 * sumaCubos (Suc n) = (Suc n * (Suc n + 1))^2" .
qed

end
</pre>

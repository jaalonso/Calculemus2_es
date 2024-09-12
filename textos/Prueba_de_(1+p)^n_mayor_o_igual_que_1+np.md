---
title: Pruebas de (1+p)^n mayor o igual que 1+np
date: 2024-09-12 06:00:00 UTC+02:00
category: Inducción
has_math: true
---

[mathjax]

Sean \\(p ∈ ℝ\\) y \\(n ∈ ℕ\\). Demostrar que si \\(p > -1\\), entonces
\\[ (1 + p)^n ≥ 1 + np \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat

variable (p : ℝ)
variable (n : ℕ)

example
  (h : p > -1)
  : (1 + p)^n ≥ 1 + n*p :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por inducción sobre \\(n\\).

**Caso base:** Sea \\(n = 0\\). Entonces,
\\begin{align}
   (1+p)^n &= (1+p)^0 \\\\
           &= 1       \\\\
           &≥ 1       \\\\
           &= 1 + 0   \\\\
           &= 1 + 0·p \\\\
           &= 1 + n·p
\\end{align}

**Paso de inducción:** Sea \\(n = m+1\\) y supongamos la hipótesis de inducción (HI)
\\[ (1 + p)^m ≥ 1 + mp \\]
Entonces,
\\begin{align}
   (1 + p)^n &= (1 + p)^(m+1)         \\\\
             &= (1 + p)^m(1 + p)      \\\\
             &≥ (1 + m * p)(1 + p)    &&\\text{[por HI]} \\\\
             &= (1 + p + mp) + m(pp)  \\\\
             &≥ 1 + p + mp            \\\\
             &= 1 + (m + 1)p          \\\\
             &= 1 + np
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat

variable (p : ℝ)
variable (n : ℕ)

-- 1ª demostración
-- ===============

example
  (h : p > -1)
  : (1 + p)^n ≥ 1 + n*p :=
by
  induction n with
  | zero =>
    -- ⊢ (1 + p) ^ 0 ≥ 1 + ↑0 * p
    have h1 : (1 + p) ^ 0 ≥ 1 + 0 * p :=
      calc (1 + p) ^ 0
           = 1           := pow_zero (1 + p)
         _ ≥ 1           := le_refl 1
         _ = 1 + 0       := (add_zero 1).symm
         _ = 1 + 0 * p   := congrArg (1 + .) (zero_mul p).symm
    exact_mod_cast h1
  | succ m HI =>
    -- m : ℕ
    -- HI : (1 + p) ^ m ≥ 1 + ↑m * p
    -- ⊢ (1 + p) ^ (m + 1) ≥ 1 + ↑(m + 1) * p
    have h1 : 1 + p > 0 := neg_lt_iff_pos_add'.mp h
    have h2 : p*p ≥ 0 := mul_self_nonneg p
    replace h2 : ↑m*(p*p) ≥ 0 := mul_nonneg (cast_nonneg m) h2
    calc (1 + p)^(m+1)
         = (1 + p)^m * (1 + p)
             := pow_succ (1 + p) m
       _ ≥ (1 + m * p) * (1 + p)
             := (mul_le_mul_right h1).mpr HI
       _ = (1 + p + m*p) + m*(p*p)
             := by ring
       _ ≥ 1 + p + m*p
             := le_add_of_nonneg_right h2
       _ = 1 + (m + 1) * p
             := by ring
       _ = 1 + ↑(m+1) * p
             := by norm_num

-- 2ª demostración
-- ===============

example
  (h : p > -1)
  : (1 + p)^n ≥ 1 + n*p :=
by
  induction n with
  | zero =>
    -- ⊢ (1 + p) ^ 0 ≥ 1 + ↑0 * p
    simp
  | succ m HI =>
    -- m : ℕ
    -- HI : (1 + p) ^ m ≥ 1 + ↑m * p
    -- ⊢ (1 + p) ^ (m + 1) ≥ 1 + ↑(m + 1) * p
    calc (1 + p)^(m+1)
         = (1 + p)^m * (1 + p)     := by rfl
       _ ≥ (1 + m * p) * (1 + p)   := by nlinarith
       _ = (1 + p + m*p) + m*(p*p) := by ring
       _ ≥ 1 + p + m*p             := by nlinarith
       _ = 1 + (m + 1) * p         := by ring
       _ = 1 + ↑(m+1) * p          := by norm_num

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- #check (add_zero a : a + 0 = a)
-- #check (cast_nonneg n : 0 ≤ ↑n)
-- #check (le_add_of_nonneg_right : 0 ≤ b → a ≤ a + b)
-- #check (le_refl a : a ≤ a)
-- #check (mul_le_mul_right : 0 < a → (b * a ≤ c * a ↔ b ≤ c))
-- #check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
-- #check (mul_self_nonneg a : 0 ≤ a * a)
-- #check (neg_lt_iff_pos_add' : -a < b ↔ 0 < a + b)
-- #check (pow_succ a n : a ^ (n + 1) = a ^ n * a)
-- #check (pow_zero a : a ^ 0 = 1)
-- #check (zero_mul a : 0 * a = 0)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Prueba_de_(1+p)^n_mayor_o_igual_que_1+np.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory "Prueba_de_(1+p)^n_mayor_o_igual_que_1+np"
imports Main HOL.Real
begin

lemma
  fixes p :: real
  assumes "p > -1"
  shows "(1 + p)^n ≥ 1 + n*p"
proof (induct n)
  show "(1 + p) ^ 0 ≥ 1 + real 0 * p"
    by simp
next
  fix n
  assume HI : "(1 + p)^n ≥ 1 +  n * p"
  have "1 + Suc n * p = 1 + (n + 1) * p"
    by simp
  also have "… = 1 + n*p + p"
    by (simp add: distrib_right)
  also have "… ≤ (1 + n*p + p) + n*(p*p)"
    by simp
  also have "… = (1 + n * p) * (1 + p)"
    by algebra
  also have "… ≤ (1 + p)^n * (1 + p)"
    using HI assms by simp
  also have "… = (1 + p)^(Suc n)"
    by simp
  finally show "1 + Suc n * p ≤ (1 + p)^(Suc n)" .
qed

end
</pre>

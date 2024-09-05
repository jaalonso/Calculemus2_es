---
title: Pruebas de "0 + 1 + 2 + 3 + ··· + n = n × (n + 1)/2"
date: 2024-09-05 06:00:00 UTC+02:00
category: Inducción
has_math: true
---

[mathjax]

Demostrar que la suma de los números naturales
\\[ 0 + 1 + 2 + 3 + ··· + n \\]
es \\(\\dfrac{n(n + 1)}{2}\\)

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Init.Data.Nat.Basic
import Mathlib.Tactic

open Nat

variable (n : Nat)

set_option pp.fieldNotation false

def suma : Nat → Nat
  | 0      => 0
  | succ n => suma n + (n+1)

example :
  2 * suma n = n * (n + 1) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea
\\[ s(n) = 0 + 1 + 2 + 3 + ··· + n \\]
Tenemos que demostrar que
\\[ s(n) = \\dfrac{n(n + 1)}{2} \\]
o, equivalentemente que
\\[ 2s(n) = n(n + 1) \\]
Lo haremos por inducción sobre \\(n\\).

**Caso base:** Sea \\(n = 0\\). Entonces,
\\begin{align}
   2s(n) &= 2s(0)     \\\\
         &= 2·0       \\\\
         &= 0         \\\\
         &= 0.(0 + 1) \\\\
         &= n.(n + 1)
\\end{align

**Paso de indución:** Sea \\(n = m+1\\) y supongamos la hipótesis de inducción (HI)
\\[ 2s(m) = m \\]
Entonces,
\\begin{align}
   2s(n) &= 2s(m+1)                \\\\
         &= 2(s(m) + (m+1))        \\\\
         &= 2s(m) + 2(m+1)         \\\\
         &= m(m + 1) + 2(m + 1)    &&\\text{[por HI]} \\\\
         &= (m + 2)(m + 1)         \\\\
         &= (m + 1)(m + 2)         \\\\
         &= n(n+1)
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Init.Data.Nat.Basic
import Mathlib.Tactic

open Nat

variable (n : Nat)

set_option pp.fieldNotation false

def suma : Nat → Nat
  | 0      => 0
  | succ n => suma n + (n+1)

@[simp]
lemma suma_zero : suma 0 = 0 := rfl

@[simp]
lemma suma_succ : suma (n + 1) = suma n + (n+1) := rfl

-- 1ª demostración
-- ===============

example :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * suma 0 = 0 * (0 + 1)
    calc 2 * suma 0
         = 2 * 0       := congrArg (2 * .) suma_zero
       _ = 0           := mul_zero 2
       _ = 0 * (0 + 1) := zero_mul (0 + 1)
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * suma n = n * (n + 1)
    -- ⊢ 2 * suma (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    := congrArg (2 * .) (suma_succ n)
       _ = 2 * suma n + 2 * (n + 1)  := mul_add 2 (suma n) (n + 1)
       _ = n * (n + 1) + 2 * (n + 1) := congrArg (. + 2 * (n + 1)) HI
       _ = (n + 2) * (n + 1)         := (add_mul n 2 (n + 1)).symm
       _ = (n + 1) * (n + 2)         := mul_comm (n + 2) (n + 1)

-- 2ª demostración
-- ===============

example :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * suma 0 = 0 * (0 + 1)
    calc 2 * suma 0
         = 2 * 0       := rfl
       _ = 0           := rfl
       _ = 0 * (0 + 1) := rfl
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * suma n = n * (n + 1)
    -- ⊢ 2 * suma (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    := rfl
       _ = 2 * suma n + 2 * (n + 1)  := by ring
       _ = n * (n + 1) + 2 * (n + 1) := by simp [HI]
       _ = (n + 2) * (n + 1)         := by ring
       _ = (n + 1) * (n + 2)         := by ring

-- 3ª demostración
-- ===============

example :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * suma 0 = 0 * (0 + 1)
    rfl
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * suma n = n * (n + 1)
    -- ⊢ 2 * suma (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    := rfl
       _ = 2 * suma n + 2 * (n + 1)  := by ring
       _ = n * (n + 1) + 2 * (n + 1) := by simp [HI]
       _ = (n + 1) * (n + 2)         := by ring

-- 4ª demostración
-- ===============

example :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero => rfl
  | succ n HI => unfold suma ; linarith [HI]

-- Lemas usados
-- ============

-- variable (a b c : ℕ)
-- #check (add_mul a b c : (a + b) * c = a * c + b * c)
-- #check (mul_add a b c : a * (b + c) = a * b + a * c)
-- #check (mul_comm a b : a * b = b * a)
-- #check (mul_zero a : a * 0 = 0)
-- #check (zero_mul a : 0 * a = 0)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Suma_de_los_primeros_n_numeros_naturales.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Suma_de_los_primeros_n_numeros_naturales
imports Main
begin

fun suma :: "nat ⇒ nat" where
  "suma 0       = 0"
| "suma (Suc n) = suma n + Suc n"

(* 1ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  have "2 * suma 0 = 2 * 0"
    by (simp only: suma.simps(1))
  also have "… = 0"
    by (rule mult_0_right)
  also have "… = 0 * (0 + 1)"
    by (rule mult_0 [symmetric])
  finally show "2 * suma 0 = 0 * (0 + 1)"
    by this
next
  fix n
  assume HI : "2 * suma n = n * (n + 1)"
  have "2 * suma (Suc n) = 2 * (suma n + Suc n)"
    by (simp only: suma.simps(2))
  also have "… = 2 * suma n + 2 * Suc n"
    by (rule add_mult_distrib2)
  also have "… = n * (n + 1) + 2 * Suc n"
    by (simp only: HI)
  also have "… = n * (n + Suc 0) + 2 * Suc n"
    by (simp only: One_nat_def)
  also have "… = n * Suc (n + 0) + 2 * Suc n"
    by (simp only: add_Suc_right)
  also have "… = n * Suc n + 2 * Suc n"
    by (simp only: add_0_right)
  also have "… = (n + 2) * Suc n"
    by (simp only: add_mult_distrib)
  also have "… = Suc (Suc n) * Suc n"
    by (simp only: add_2_eq_Suc')
  also have "… = (Suc n + 1) * Suc n"
    by (simp only: Suc_eq_plus1)
  also have "… = Suc n * (Suc n + 1)"
    by (simp only: mult.commute)
  finally show "2 * suma (Suc n) = Suc n * (Suc n + 1)"
    by this
qed

(* 2ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  have "2 * suma 0 = 2 * 0" by simp
  also have "… = 0" by simp
  also have "… = 0 * (0 + 1)" by simp
  finally show "2 * suma 0 = 0 * (0 + 1)" .
next
  fix n
  assume HI : "2 * suma n = n * (n + 1)"
  have "2 * suma (Suc n) = 2 * (suma n + Suc n)" by simp
  also have "… = 2 * suma n + 2 * Suc n" by simp
  also have "… = n * (n + 1) + 2 * Suc n" using HI by simp
  also have "… = n * (n + Suc 0) + 2 * Suc n" by simp
  also have "… = n * Suc (n + 0) + 2 * Suc n" by simp
  also have "… = n * Suc n + 2 * Suc n" by simp
  also have "… = (n + 2) * Suc n" by simp
  also have "… = Suc (Suc n) * Suc n" by simp
  also have "… = (Suc n + 1) * Suc n" by simp
  also have "… = Suc n * (Suc n + 1)" by simp
  finally show "2 * suma (Suc n) = Suc n * (Suc n + 1)" .
qed

(* 3ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  have "2 * suma 0 = 2 * 0" by simp
  also have "… = 0" by simp
  also have "… = 0 * (0 + 1)" by simp
  finally show "2 * suma 0 = 0 * (0 + 1)" .
next
  fix n
  assume HI : "2 * suma n = n * (n + 1)"
  have "2 * suma (Suc n) = 2 * (suma n + Suc n)" by simp
  also have "… = n * (n + 1) + 2 * Suc n" using HI by simp
  also have "… = (n + 2) * Suc n" by simp
  also have "… = Suc n * (Suc n + 1)" by simp
  finally show "2 * suma (Suc n) = Suc n * (Suc n + 1)" .
qed

(* 4ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  show "2 * suma 0 = 0 * (0 + 1)" by simp
next
  fix n
  assume "2 * suma n = n * (n + 1)"
  then show "2 * suma (Suc n) = Suc n * (Suc n + 1)" by simp
qed

(* 5ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* 6ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
by (induct n) simp_all

end
</pre>

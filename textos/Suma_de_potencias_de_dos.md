---
title: Pruebas de ∑k<n. 2ᵏ = 2ⁿ-1
date: 2024-09-23 06:00:00 UTC+02:00
category: Sumatorio
has_math: true
status: draft
---

Demostrar que
\\[ 1 + 2 + 2^2 + 2^3 + ... + 2^{n-1} = 2^n - 1 \\]

Para ello, completar la siguiente teoría de Lean4:

~~~lean
import Mathlib.Tactic

open Finset Nat

variable (n : ℕ)

example :
  ∑ k in range n, 2^k = 2^n - 1 :=
by sorry
~~~
<!-- TEASER_END -->

# 1. Demostración en lenguaje natural

Por indución en \\(n\\).

Caso base: Sea \\(n = 0\\). Entonces,
\\begin{align}
   \\sum_{k<0} 2^k &= 0        \\newline
                  &= 2^0 - 1  \\newline
                  &= 2^n - 1  \\newline
\\end{align}

Paso de inducción: Sea \\(n = m+1\\) y supongamos la hipótesis de inducción (HI)
\\[ \\sum_{k<m} 2^k = 2^m-1 \\]
Entonces,
\\begin{align}
   \\sum_{k<n} 2^k &= \\sum_{k<m+1} 2^k      \\newline
                  &= \\sum_{k<m} 2^k + 2^m  \\newline
                  &= (2^m - 1) + 2^m       &&\\text{[por HI]} \\newline
                  &= (2^m + 2^m) - 1       \\newline
                  &= 2^{m + 1} - 1         \\newline
                  &= 2^n - 1
\\end{align}

# 2. Demostraciones con Lean4

~~~lean
import Mathlib.Tactic

open Finset Nat

variable (n : ℕ)

-- 1ª demostración
-- ===============

example :
  ∑ k in range n, 2^k = 2^n - 1 :=
by
  induction n with
  | zero =>
    -- ⊢ ∑ k ∈ range 0, 2 ^ k = 2 ^ 0 - 1
    calc ∑ k ∈ range 0, 2 ^ k
         = 0                   := sum_range_zero (2 ^ .)
       _ = 2 ^ 0 - 1           := by omega
  | succ m HI =>
    -- m : ℕ
    -- HI : ∑ k ∈ range m, 2 ^ k = 2 ^ m - 1
    -- ⊢ ∑ k ∈ range (m + 1), 2 ^ k = 2 ^ (m + 1) - 1
    have h1 : (2^m - 1) + 2^m = (2^m + 2^m) - 1 := by
      have h2 : 2^m ≥ 1 := Nat.one_le_two_pow
      omega
    calc ∑ k in range (m + 1), 2^k
       = ∑ k in range m, (2^k) + 2^m
           := sum_range_succ (2 ^ .) m
     _ = (2^m - 1) + 2^m
           := congrArg (. + 2^m) HI
     _ = (2^m + 2^m) - 1
           := h1
     _ = 2^(m + 1) - 1
           := congrArg (. - 1) (two_pow_succ m).symm

-- 2ª demostración
-- ===============

example :
  ∑ k in range n, 2^k = 2^n - 1 :=
by
  induction n with
  | zero =>
    -- ⊢ ∑ k ∈ range 0, 2 ^ k = 2 ^ 0 - 1
    simp
  | succ m HI =>
    -- m : ℕ
    -- HI : ∑ k ∈ range m, 2 ^ k = 2 ^ m - 1
    -- ⊢ ∑ k ∈ range (m + 1), 2 ^ k = 2 ^ (m + 1) - 1
    have h1 : (2^m - 1) + 2^m = (2^m + 2^m) - 1 := by
      have h2 : 2^m ≥ 1 := Nat.one_le_two_pow
      omega
    calc ∑ k in range (m + 1), 2^k
       = ∑ k in range m, (2^k) + 2^m := sum_range_succ (2 ^ .) m
     _ = (2^m - 1) + 2^m             := by linarith
     _ = (2^m + 2^m) - 1             := h1
     _ = 2^(m + 1) - 1               := by omega

-- Lemas usados
-- ============

-- variable (f : ℕ → ℕ)
-- #check (Nat.one_le_two_pow : 1 ≤ 2 ^ n)
-- #check (Nat.two_pow_succ n : 2 ^ (n + 1) = 2 ^ n + 2 ^ n)
-- #check (sum_range_succ f n : ∑ x ∈ range (n+1), f x = ∑ x ∈ range n, f x + f n)
-- #check (sum_range_zero f : ∑ k ∈ range 0, f k = 0)
~~~

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Suma_de_potencias_de_dos.lean).

# 3. Demostraciones con Isabelle/HOL

~~~isabelle
theory Suma_de_potencias_de_dos
imports Main
begin

(* 1ª demostración *)
lemma "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  show "(∑k≤0. (2::nat)^k) = 2^(0+1) - 1"
    by simp
next
  fix n
  assume HI : "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
  have "(∑k≤Suc n. (2::nat)^k) =
        (∑k≤n. (2::nat)^k) + 2^Suc n"
    by simp
  also have "… = (2^(n+1) - 1) + 2^Suc n"
    using HI by simp
  also have "… = 2^(Suc n + 1) - 1"
    by simp
  finally show "(∑k≤Suc n. (2::nat)^k) = 2^(Suc n + 1) - 1" .
qed

(* 2ª demostración *)
lemma "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  show "(∑k≤0. (2::nat)^k) = 2^(0+1) - 1"
    by simp
next
  fix n
  assume HI : "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
  have "(∑k≤Suc n. (2::nat)^k) =
        (2^(n+1) - 1) + 2^Suc n"
    using HI by simp
  then show "(∑k≤Suc n. (2::nat)^k) = 2^(Suc n + 1) - 1"
    by simp
qed

(* 3ª demostración *)
lemma "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* 4ª demostración *)
lemma "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
by (induct n) simp_all

end
~~~

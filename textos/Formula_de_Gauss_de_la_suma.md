---
title: Pruebas de "∑_{i<n} i = n(n-1)/2"
date: 2024-09-19 06:00:00 UTC+02:00
category: Sumatorios
has_math: true
---

La fórmula de Gauss para la suma de los primeros números naturales es
\\[ 0 + 1 + 2 + ... + (n-1) = \\dfrac{n(n-1)}{2} \\]
es decir,
\\[ \\sum_{i < n} i = \\dfrac{n(n-1)}{2} \\]

En un ejercicio anterior se ha demostrado dicha fórmula por inducción. Otra forma de demostrarla, sin usar inducción, es la siguiente: La suma se puede escribir de dos maneras
\\begin{align}
   S &= &0     &+ &1     &+ &2     &+ ... &+ &(n-3) &+ &(n-2) &+ &(n-1) \\newline
   S &= &(n-1) &+ &(n-2) &+ &(n-3) &+ ... &+ &2     &+ &1     &+ &0
\\end{align}
Al sumar, se observa que cada par de números de la misma columna da como suma (n-1), y puesto que hay n columnas en total, se sigue
\\[ 2S = n(n-1) \\]
lo que prueba la fórmula.

Demostrar la fórmula de Gauss siguiendo el procedimiento anterior.

Para ello, completar la siguiente teoría de Lean4:

~~~lean
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset Nat

variable (n i : ℕ)

example :
  ∑ i ∈ range n, i = n * (n - 1) / 2 :=
by sorry
~~~
<!-- TEASER_END -->

# 1. Demostración en lenguaje natural

Basta demostrar que
\\[ 2\\sum_{i<n} i = n(n-1) \\]
que se demuestra por la siguiente cadena de igualdades
\\begin{align}
   2\\sum_{i<n} i
   &= \\sum_{i<n} i + \\sum_{i<n} i \\newline
   &= \\sum_{i<n} i + \\sum_{i<n} ((n - 1) - i) \\newline
   &= \\sum_{i<n} (i + ((n - 1) - i)) \\newline
   &= \\sum_{i<n} (n - 1) \\newline
   &= n(n - 1)
\\end{align}

# 2. Demostraciones con Lean4

~~~lean
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset Nat

variable (n i : ℕ)

-- Lema auxiliar
-- =============

-- Se usará el siguiente lema auxiliar del que se presentan distintas
-- demostraciones.

-- 1ª demostración del lema auxiliar
example :
  ∀ x, x ∈ range n → x + (n - 1 - x) = n - 1 :=
by
  intros x hx
  -- x : ℕ
  -- hx : x ∈ range n
  -- ⊢ x + ((n - 1) - x) = n - 1
  replace hx : x < n := mem_range.mp hx
  replace hx : x ≤ n - 1 := le_pred_of_lt hx
  exact add_sub_of_le hx

-- 2ª demostración del lema auxiliar
example :
  ∀ x, x ∈ range n → x + (n - 1 - x) = n - 1 :=
by
  intros x hx
  -- x : ℕ
  -- hx : x ∈ range n
  -- ⊢ x + (n - 1 - x) = n - 1
  exact add_sub_of_le (le_pred_of_lt (mem_range.1 hx))

-- 3ª demostración del lema auxiliar
lemma auxiliar :
  ∀ x, x ∈ range n → x + (n - 1 - x) = n - 1 :=
fun _ hx ↦ add_sub_of_le (le_pred_of_lt (mem_range.1 hx))

-- Lema principal
-- ==============

-- 1ª demostración
example :
  ∑ i ∈ range n, i = n * (n - 1) / 2 :=
by
  suffices _ : (∑ i ∈ range n, i) * 2 = n * (n - 1) by omega
  calc (∑ i ∈ range n, i) * 2
       = (∑ i ∈ range n, i) + (∑ i ∈ range n, i)
           := mul_two _
     _ = (∑ i ∈ range n, i) + (∑ i ∈ range n, (n - 1 - i))
           := congrArg ((∑ i ∈ range n, i) + .) (sum_range_reflect id n).symm
     _ = ∑ i ∈ range n, (i + (n - 1 - i))
           := sum_add_distrib.symm
     _ = ∑ i ∈ range n, (n - 1)
           := sum_congr rfl (by exact fun x a => auxiliar n x a)
     _ = card (range n) • (n - 1)
           := sum_const (n - 1)
     _ = card (range n) * (n - 1)
           := nsmul_eq_mul _ _
     _ = n * (n - 1)
           := congrArg (. * (n - 1)) (card_range n)

-- 2ª demostración
example :
  ∑ i ∈ range n, i = n * (n - 1) / 2 :=
by
  suffices _ : (∑ i ∈ range n, i) * 2 = n * (n - 1) by omega
  calc (∑ i ∈ range n, i) * 2
       = (∑ i ∈ range n, i) + (∑ i ∈ range n, (n - 1 - i))
           := by rw [sum_range_reflect (fun i => i) n, mul_two]
     _ = ∑ i ∈ range n, (i + (n - 1 - i))
           := sum_add_distrib.symm
     _ = ∑ i ∈ range n, (n - 1)
           := sum_congr rfl (auxiliar n)
     _ = n * (n - 1)
           := by rw [sum_const, card_range, Nat.nsmul_eq_mul]

-- 3ª demostración
example :
  ∑ i ∈ range n, i = n * (n - 1) / 2 :=
by
  suffices _ : (∑ i ∈ range n, i) * 2 = n * (n - 1) by omega
  show (∑ i ∈ range n, i) * 2 = n * (n - 1)
  exact sum_range_id_mul_two n

-- 4ª demostración
example :
  ∑ i ∈ range n, i = n * (n - 1) / 2 :=
by
  rw [← sum_range_id_mul_two n]
  -- ⊢ ∑ i ∈ range n, i = (∑ i ∈ range n, i) * 2 / 2
  rw [Nat.mul_div_cancel _ zero_lt_two]

-- 5ª demostración
example :
  (∑ i ∈ range n, i) = n * (n - 1) / 2 :=
sum_range_id n

-- Lemas usados
-- ============

-- variable (m : ℕ)
-- variable (f g : ℕ → ℕ)
-- variable (s t : Finset ℕ)
-- #check (Nat.mul_div_cancel m : 0 < n → m * n / n = m)
-- #check (add_sub_of_le : n ≤ m → n + (m - n) = m)
-- #check (card_range n : card (range n) = n)
-- #check (le_pred_of_lt : n < m → n ≤ m - 1)
-- #check (mem_range : m ∈ range n ↔ m < n)
-- #check (mul_two n : n * 2 = n + n)
-- #check (nsmul_eq_mul m n : m • n = m * n)
-- #check (sum_add_distrib :  ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x)
-- #check (sum_congr : s = t → (∀ x ∈ t, f x = g x) → s.sum f = t.sum g)
-- #check (sum_const m : ∑ _ ∈ s, m = card s • m)
-- #check (sum_range_id n : ∑ i ∈ range n, i = n * (n - 1) / 2)
-- #check (sum_range_id_mul_two n : (∑ i ∈ range n, i) * 2 = n * (n - 1))
-- #check (sum_range_reflect f n : ∑ j ∈ range n, f (n - 1 - j) = ∑ j ∈ range n, f j)
~~~

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Formula_de_Gauss_de_la_suma.lean).

# 3. Demostraciones con Isabelle/HOL

~~~isabelle
theory Formula_de_Gauss_de_la_suma
imports Main
begin

lemma
  fixes n :: nat
  shows "2 * (∑i<n. i) = n * (n - 1)"
proof -
  have "2 * (∑i<n. i) = (∑i<n. i) + (∑i<n. i)"
    by simp
  also have "… = (∑i<n. i) + (∑i<n. n - Suc i)"
    using sum.nat_diff_reindex [where g = id] by auto
  also have "… = (∑i<n. (i + (n - Suc i)))"
    using sum.distrib [where A = "{..<n}" and
                             g = id and
                             h = "λi. n - Suc i"] by auto
  also have "… = (∑i<n. n - 1)"
    by simp
  also have "… = n * (n -1)"
    using sum_constant by auto
  finally show "2 * (∑i<n. i) = n * (n - 1)" .
qed

end
~~~

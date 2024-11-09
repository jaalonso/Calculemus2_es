---
title: Si el límite de \(u_n\) es \(a\), entonces el de \(7u_n\) es \(7a\)
date: 2024-11-09 06:00:00 UTC+02:00
category: Límites
has_math: true
---

En Lean, una sucesión \\(u_0, u_1, u_2, ...\\) se puede representar mediante una función \\(u : ℕ → ℝ\\) de forma que \\(u(n)\\) es \\(u_n\\).

Se define que \\(a\\) es el límite de la sucesión \\(u\\), por
~~~lean
   def limite : (ℕ → ℝ) → ℝ → Prop :=
     fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
~~~

Demostrar que que si el límite de \\(u_n\\) es \\(a\\), entonces el de \\(7u_n\\) es \\(7a\\).

Para ello, completar la siguiente teoría de Lean4:

~~~lean
import Mathlib.Tactic

variable {u : ℕ → ℝ}
variable {a : ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (h : limite u a)
  : limite (fun n ↦ 7 * u n) (7 * a) :=
by sorry
~~~
<!-- TEASER_END -->

# 1. Demostración en lenguaje natural

Sea \\(ε > 0\\). Tenemos que demostrar que, existe un \\(N ∈ ℕ\\) tal que
\\[ (∀ n ∈ ℕ)[N ≤ n → |7u_n - 7a| < ε] \\tag{1} \\]
Puesto que el límite de \\(u_n\\) es \\(a\\), existe un \\(N ∈ ℕ\\) tal que
\\[ (∀ n ∈ ℕ)\\left[N ≤ n → |u_n - a| < \\dfrac{ε}{7}\\right] \\tag{2} \\]
Sea \\(N ∈ ℕ\\) que verifica (2), veamos que el mismo \\(N\\) verifica (1). Para ello, sea \\(n ∈ ℕ\\) tal que \\(N ≤ n\\). Entonces,
\\begin{align}
   |7u_n - 7a| &= |7(u_n - a)|         \\\\
               &= |7||u_n - a|         \\\\
               &= 7|u_n - a|           \\\\
               &< 7\\dfrac{ε}{7}        &&\\text{[por (2)]} \\\\
               &= ε
\\end{align}

# 2. Demostraciones con Lean4

~~~lean
import Mathlib.Tactic

variable {u : ℕ → ℝ}
variable {a : ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ 7 * u n) (7 * a) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(fun n => 7 * u n) n - 7 * a| < ε
  dsimp
  -- ⊢ ∃ N, ∀ n ≥ N, |7 * u n - 7 * a| < ε
  specialize h (ε / 7) (by linarith)
  -- h : ∃ N, ∀ n ≥ N, |u n - a| < ε / 7
  obtain ⟨N, hN⟩ := h
  -- N : ℕ
  -- hN : ∀ n ≥ N, |u n - a| < ε / 7
  use N
  -- ⊢ ∀ n ≥ N, |7 * u n - 7 * a| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |7 * u n - 7 * a| < ε
  specialize hN n hn
  -- hN : |u n - a| < ε / 7
  calc |7 * u n - 7 * a|
     = |7 * (u n - a)|    := by rw [← mul_sub]
   _ = |7| * |u n - a|    := by rw [abs_mul]
   _ = 7 * |u n - a|      := by congr ; simp [Nat.abs_ofNat]
   _ < 7 * (ε / 7)        := by simp [Nat.ofNat_pos, mul_lt_mul_left, hN]
   _ = ε                  := mul_div_cancel₀ ε (OfNat.zero_ne_ofNat 7).symm

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ 7 * u n) (7 * a) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(fun n => 7 * u n) n - 7 * a| < ε
  dsimp
  -- ⊢ ∃ N, ∀ n ≥ N, |7 * u n - 7 * a| < ε
  obtain ⟨N, hN⟩ := h (ε / 7) (by linarith)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |u n - a| < ε / 7
  use N
  -- ⊢ ∀ n ≥ N, |7 * u n - 7 * a| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ ⊢ |7 * u n - 7 * a| < ε
  specialize hN n hn
  -- hN : |u n - a| < ε / 7
  rw [← mul_sub]
  -- ⊢ |7 * (u n - a)| < ε
  rw [abs_mul]
  -- ⊢ |7| * |u n - a| < ε
  rw [abs_of_nonneg]
  . -- ⊢ 7 * |u n - a| < ε
    linarith
  . -- ⊢ 0 ≤ 7
    exact Nat.ofNat_nonneg' 7

-- 3ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ 7 * u n) (7 * a) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(fun n => 7 * u n) n - 7 * a| < ε
  dsimp
  -- ⊢ ∃ N, ∀ n ≥ N, |7 * u n - 7 * a| < ε
  obtain ⟨N, hN⟩ := h (ε / 7) (by linarith)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |u n - a| < ε / 7
  use N
  -- ⊢ ∀ n ≥ N, |7 * u n - 7 * a| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ ⊢ |7 * u n - 7 * a| < ε
  specialize hN n hn
  -- hN : |u n - a| < ε / 7
  rw [← mul_sub, abs_mul, abs_of_nonneg] <;> linarith

-- Lemas usados
-- ============

-- variable (b c : ℝ)
-- variable (n : ℕ)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (abs_of_nonneg : 0 ≤ a → |a| = a)
-- #check (mul_div_cancel₀ a : b ≠ 0 → b * (a / b) = a)
-- #check (mul_lt_mul_left : 0 < a → (a * b < a * c ↔ b < c))
-- #check (mul_sub a b c : a * (b - c) = a * b - a * c)
~~~

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Limite_de_7u.lean).

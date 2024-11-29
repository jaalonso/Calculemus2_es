---
title: If u(n) tends to a, then 7u(n) tends to 7a
date: 2024-11-10 06:00:00 UTC+02:00
category: Limits
has_math: true
---

In Lean, a sequence \\(u_0, u_1, u_2, ...\\) can be represented by a function \\(u : ℕ → ℝ\\) such that \\(u(n)\\) is the term \\(u_n\\).

We define that \\(u\\) tends to \\(a\\) by
~~~lean
   def tendsTo : (ℕ → ℝ) → ℝ → Prop :=
     fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
~~~

Prove that if \\(u_n\\) tends to \\(a\\), then \\(7u\\_n\\) tends to \\(7a\\).

To do this, complete the following Lean4 theory:

~~~lean
import Mathlib.Tactic

variable {u : ℕ → ℝ}
variable {a : ℝ}

def tendsTo : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (h : tendsTo u a)
  : tendsTo (fun n ↦ 7 * u n) (7 * a) :=
by sorry
~~~
<!-- TEASER_END -->

# 1. Proof in natural language

Let \\(ε > 0\\). We need to prove that there exists an \\(N ∈ ℕ\\) such that
\\[ (∀ n ∈ ℕ)[N ≤ n → |7u_n - 7a| < ε] \\tag{1} \\]
Since \\(u_n\\) tends to \\(a\\), there exists an \\(N ∈ ℕ\\) such that
\\[ (∀ n ∈ ℕ)\\left[N ≤ n → |u_n - a| < \\dfrac{ε}{7}\\right] \\tag{2} \\]
Let \\(N ∈ ℕ\\) that satisfies (2), let's see that the same \\(N\\) satisfies (1). For this, let \\(n ∈ ℕ\\) such that \\(N ≤ n\\). Then,
\\begin{align}
   |7u_n - 7a| &= |7(u_n - a)|    \\newline
               &= |7||u_n - a|    \\newline
               &= 7|u_n - a|      \\newline
               &< 7(ε / 7)        &&\\text{[by (2)]} \\newline
               &= ε
\\end{align}

# 2. Proofs with Lean4

~~~lean
import Mathlib.Tactic

variable {u : ℕ → ℝ}
variable {a : ℝ}

def tendsTo : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- Proof 1
-- =======

example
  (h : tendsTo u a)
  : tendsTo (fun n ↦ 7 * u n) (7 * a) :=
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

-- Proof 2
-- =======

example
  (h : tendsTo u a)
  : tendsTo (fun n ↦ 7 * u n) (7 * a) :=
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

-- Proof 3
-- =======

example
  (h : tendsTo u a)
  : tendsTo (fun n ↦ 7 * u n) (7 * a) :=
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

-- Used lemmas
-- ===========

-- variable (b c : ℝ)
-- variable (n : ℕ)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (abs_of_nonneg : 0 ≤ a → |a| = a)
-- #check (mul_div_cancel₀ a : b ≠ 0 → b * (a / b) = a)
-- #check (mul_lt_mul_left : 0 < a → (a * b < a * c ↔ b < c))
-- #check (mul_sub a b c : a * (b - c) = a * b - a * c)
~~~

You can interact with the previous proofs at [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Limit_of_7u.lean).

# Referencias

+ Kevin Buzzard. [Formalising Mathematics (2024), Section02reals, Sheet6.lean](https://github.com/ImperialCollegeLondon/formalising-mathematics-2024/blob/main/FormalisingMathematics2024/Section02reals/Sheet6.lean).

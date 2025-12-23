---
Título: La sucesión constante aₙ = L converge a L
Autor:  José A. Alonso
---

[mathjax]

En Lean, una sucesión \\(a₀, a₁, a₂, ...\\) se puede representar mediante una función \\((a : ℕ → ℝ)\\) de forma que \\(a(n)\\) es \\(aₙ\\).

Se define que \\(L\\) es el límite de la sucesión \\(a\\), por
<pre lang="text">
def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
</pre>

Demostrar que si para todo \\(n\\), \\(aₙ = L\\), entonces la sucesión \\(a\\) converge a \\(L\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a : ℕ → ℝ)
variable (L : ℝ)

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que para cada \\(ε ∈ ℝ\\) tal que \\(ε > 0\\), existe un \\(N ∈ ℕ\\), tal que \\((∀n ∈ ℕ)[n ≥ N → |a(n) - L| < ε]\\). Basta tomar \\(N\\) como \\(0\\), ya que para todo \\(n ≥ N\\) se tiene
\\begin{align}
   |a(n) - L| &= |L - L| \\\\
              &= |0|     \\\\
              &= 0       \\\\
              &< ε       \\\\
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a : ℕ → ℝ)
variable (L : ℝ)

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

-- 1ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by
  change ∀ ε > 0 , ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
  -- ⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |a n - L| < ε
  use 0
  -- ⊢ ∀ n ≥ 0, |a n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ 0
  -- ⊢ |a n - L| < ε
  specialize h n
  -- h : a n = L
  rewrite [h]
  -- ⊢ |L - L| < ε
  ring_nf
  -- ⊢ |0| < ε
  norm_num
  -- ⊢ 0 < ε
  exact hε

-- 2ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |a n - L| < ε
  use 0
  -- ⊢ ∀ (n : ℕ), n ≥ 0 → |a n - L| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ 0
  -- ⊢ |a n - L| < ε
  show |a n - L| < ε
  calc |a n - L| = |L - L| := by rw [h n]
               _ = |0|     := by {congr ; exact sub_self L}
               _ = 0       := abs_zero
               _ < ε       := hε

-- 3ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |a n - L| < ε
  use 0
  -- ⊢ ∀ (n : ℕ), n ≥ 0 → |a n - L| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ 0
  -- ⊢ |a n - L| < ε
  show |a n - L| < ε
  calc |a n - L| = 0 := by simp [h n]
               _ < ε := hε

-- 4ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |a n - L| < ε
  aesop

-- 5ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |a n - L| < ε
  aesop

-- 6ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : LimSuc a L :=
fun ε hε ↦ by aesop

-- Lemas usados
-- ============

#check (sub_self a : a - a = 0)
</pre>

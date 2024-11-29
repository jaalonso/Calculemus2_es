---
title: Si el límite de la sucesión u(n) es a y c ∈ ℝ, entonces el límite de u(n)c es ac
date: 2024-11-29 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

En Lean, una sucesión \\(u\\_0, u\\_1, u\\_2, ...\\) se puede representar mediante una función \\(u : ℕ → ℝ\\) de forma que \\(u(n)\\) es \\u\\_n\\).

Se define que \\(a\\) es el límite de la sucesión \\(u\\), por
<pre lang="lean">
   def limite : (ℕ → ℝ) → ℝ → Prop :=
     fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
</pre>

Demostrar que que si el límite de \\(u\\_n) es \\(a\\), entonces el de \\(u\\_n c\\) es \\(ac\\).

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u : ℕ → ℝ)
variable (a c : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (h : limite u a)
  : limite (fun n ↦ (u n) * c) (a * c) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

En un [ejercicio anterior](https://tinyurl.com/2244qcxs) se han presentado demostraciones de la siguiente propiedad
#+begin_quote
"Si el límite de la sucesión \\(u\\_n\\) es \\(a\\) y \\(c ∈ ℝ\\), entonces el límite de \\(cu\\_n\\) es \\(ca\\)."
#+end_quote

A partir de dicha propiedad se demuestra que
#+begin_quote
Si el límite de la sucesión \\(u\\_n\\) es \\(a\\) y \\(c ∈ ℝ\\), entonces el límite de \\(u\\_nc\\) es \\(ac\\)."
#+end_quote
En efecto, supongamos que
\\[ \\text{el límite de \\(u\\_n\\) es \\(a\\)} \\]
Entonces, por la propiedad anterior,
\\[ \\text{el límite de \\(cu\\_n\\) es \\(ca\\)}  \\tag{1} \\]
Pero, por la conmutatividad del producto, se tiene que
\\begin{align*}
   (∀n ∈ ℕ)[cu\\_n = u\\_nc] \\tag{2} \\\\
   ca = ac                 \\tag{3}
\\end{align*}
Por (1), (2) y (3) se tiene que
\\[ \\text{el límite de \\(u\\_nc\\) es \\(ac\\) \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u : ℕ → ℝ)
variable (a c : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- Se usa el siguiente teorema demostrado en un ejercicio anterior.

theorem limite_por_const
  (h : limite u a)
  : limite (fun n ↦ c * (u n)) (c * a) :=
by
  by_cases hc : c = 0
  . -- hc : c = 0
    subst hc
    -- ⊢ limite (fun n => 0 * u n) (0 * a)
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => 0 * u n) n - 0 * a| < ε
    aesop
  . -- hc : ¬c = 0
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    have hc' : 0 < |c| := abs_pos.mpr hc
    have hεc : 0 < ε / |c| := div_pos hε hc'
    specialize h (ε/|c|) hεc
    -- h : ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    cases' h with N hN
    -- N : ℕ
    -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    use N
    -- ⊢ ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    intros n hn
    -- n : ℕ
    -- hn : n ≥ N
    -- ⊢ |(fun n => c * u n) n - c * a| < ε
    specialize hN n hn
    -- hN : |u n - a| < ε / |c|
    dsimp only
    calc |c * u n - c * a|
         = |c * (u n - a)| := congr_arg abs (mul_sub c (u n) a).symm
       _ = |c| * |u n - a| := abs_mul c  (u n - a)
       _ < |c| * (ε / |c|) := (mul_lt_mul_left hc').mpr hN
       _ = ε               := mul_div_cancel₀ ε (ne_of_gt hc')

example
  (h : limite u a)
  : limite (fun n ↦ (u n) * c) (a * c) :=
by
  have h1 : ∀ n, (u n) * c = c * (u n) := by
    intro
    -- n : ℕ
    -- ⊢ u n * c = c * u n
    ring
  have h2 : a * c = c * a := mul_comm a c
  simp [h1,h2]
  -- ⊢ limite (fun n => c * u n) (c * a)
  exact limite_por_const u a c h

-- Lemas usados
-- ============

-- variable (b c : ℝ)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (abs_pos.mpr : a ≠ 0 → 0 < |a|)
-- #check (div_pos : 0 < a → 0 < b → 0 < a / b)
-- #check (lt_div_iff₀' : 0 < c → (a < b / c ↔ c * a < b))
-- #check (mul_comm a b : a * b = b * a)
-- #check (mul_div_cancel₀ a : b ≠ 0 → b * (a / b) = a)
-- #check (mul_lt_mul_left : 0 < a → (a * b < a * c ↔ b < c))
-- #check (mul_sub a b c : a * (b - c) = a * b - a * c)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Limite_multiplicado_por_una_constante_2.lean).

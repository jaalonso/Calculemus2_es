---
title: Si x es el supremo de A, entonces ((∀ y)[y < x → (∃ a ∈ A)[y < a]])
date: 2024-08-30 06:00:00 UTC+02:00
category: Números reales
has_math: true
---

[mathjax]

En Lean4 se puede definir que \(x\) es una cota superior de \(A\) por
<pre lang="haskell">
   def cota_superior (A : set ℝ) (x : ℝ) :=
     ∀ a ∈ A, a ≤ x
</pre>
y \(x\) es el supremo de \(A\) por
<pre lang="haskell">
   def es_supremo (A : set ℝ) (x : ℝ) :=
     cota_superior A x ∧ ∀ y, cota_superior A y → x ≤ y
</pre>

Demostrar que si \(x\) es supremo de \(A\), entonces
\[ (∀ y)[y < x → (∃ a ∈ A)[y < a]] \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {A : Set ℝ}
variable {x : ℝ}

def cota_superior (A : Set ℝ) (x : ℝ) :=
  ∀ a ∈ A, a ≤ x

def es_supremo (A : Set ℝ) (x : ℝ) :=
  cota_superior A x ∧ ∀ y, cota_superior A y → x ≤ y

-- 1ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \(y < x\). Demostraremos que
\[ (∃ a ∈ A)[y < a] \]
por reducción al absurdo. Para ello, supongamos que
\[ (∀ a ∈ A)[a ≤ y] \]
Entonces, \(y\) es una cota superior de \(A\) y, como \(x\) es supremo de \(A\), se tiene que \(x ≤ y\) en contradicción con \(y < x\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {A : Set ℝ}
variable {x : ℝ}

def cota_superior (A : Set ℝ) (x : ℝ) :=
  ∀ a ∈ A, a ≤ x

def es_supremo (A : Set ℝ) (x : ℝ) :=
  cota_superior A x ∧ ∀ y, cota_superior A y → x ≤ y

-- 1ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  have h1 : cota_superior A y := h
  have h2 : x ≤ y := hx.2 y h1
  have h3 : ¬x ≤ y := not_le.mpr hy
  exact h3 h2

-- 2ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  have h1 : x ≤ y := hx.2 y h
  replace h1 : ¬(y < x) := not_lt_of_le h1
  exact h1 hy

-- 3ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  apply absurd hy
  -- ⊢ ¬y < x
  apply not_lt_of_le
  -- ⊢ x ≤ y
  apply hx.2 y
  -- ⊢ cota_superior A y
  exact h

-- 4ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  exact absurd hy (not_lt_of_le (hx.2 y h))

-- 5ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  contrapose hy
  -- hy : ¬∃ a ∈ A, y < a
  -- ⊢ ¬y < x
  push_neg at hy
  -- hy : ∀ a ∈ A, a ≤ y
  push_neg
  -- ⊢ x ≤ y
  unfold es_supremo at hx
  -- hx : cota_superior A x ∧ ∀ (y : ℝ), cota_superior A y → x ≤ y
  rcases hx with ⟨_, h2⟩
  -- h2 : ∀ (y : ℝ), cota_superior A y → x ≤ y
  apply h2 y
  -- h2 : ∀ (y : ℝ), cota_superior A y → x ≤ y
  unfold cota_superior
  -- ⊢ ∀ a ∈ A, a ≤ y
  exact hy

-- 6ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  contrapose hy
  -- hy : ¬∃ a ∈ A, y < a
  -- ⊢ ¬y < x
  push_neg at hy
  -- hy : ∀ a ∈ A, a ≤ y
  push_neg
  -- ⊢ x ≤ y
  rcases hx with ⟨-, h2⟩
  -- h2 : ∀ (y : ℝ), cota_superior A y → x ≤ y
  exact h2 y hy

-- 7ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  contrapose hy
  -- hy : ¬∃ a ∈ A, y < a
  -- ⊢ ¬y < x
  push_neg at hy
  -- hy : ∀ a ∈ A, a ≤ y
  push_neg
  -- ⊢ x ≤ y
  exact hx.right y hy

-- 8ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intro y
  -- y : ℝ
  -- ⊢ y < x → ∃ a ∈ A, y < a
  contrapose!
  -- ⊢ (∀ a ∈ A, a ≤ y) → x ≤ y
  exact hx.right y

-- 9ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intro y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  exact (lt_isLUB_iff hx).mp hy

-- 10ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
fun _ hy ↦ (lt_isLUB_iff hx).mp hy

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- variable (p q : Prop)
-- #check (absurd : p → ¬p → q)
-- #check (lt_isLUB_iff : IsLUB A a → (b < a ↔ ∃ c ∈ A, b < c))
-- #check (not_le : ¬a ≤ b ↔ b < a)
-- #check (not_lt_of_le : a ≤ b → ¬b < a)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Si_x_es_el_supremo_de_A_entonces_forall_y_y_lt_x_to_exists_a_in_A_y_lt_a.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory "Si_x_es_el_supremo_de_A_entonces_forall_y_y_lt_x_to_exists_a_in_A_y_lt_a"
  imports Main HOL.Real
begin

definition cota_superior :: "(real set) ⇒ real ⇒ bool" where
  "cota_superior A x ⟷ (∀a∈A. a ≤ x)"

definition es_supremo :: "(real set) ⇒ real ⇒ bool" where
  "es_supremo A x ⟷ (cota_superior A x ∧
                       (∀ y. cota_superior A y ⟶ x ≤ y))"

(* 1ª demostración *)
lemma
  assumes "es_supremo A x"
  shows   "∀y<x. ∃a∈A. y < a"
proof (intro allI impI)
  fix y
  assume "y < x"
  show "∃a∈A. y < a"
  proof (rule ccontr)
    assume "¬ (∃a∈A. y < a)"
    then have "∀a∈A. a ≤ y"
      by auto
    then have "cota_superior A y"
      using cota_superior_def by simp
    then have "x ≤ y"
      using assms es_supremo_def by simp
    then have "x < x"
      using ‹y < x› by simp
    then show False by simp
  qed
qed

(* 2ª demostración *)
lemma
  assumes "es_supremo A x"
  shows   "∀y<x. ∃a∈A. y < a"
proof (intro allI impI)
  fix y
  assume "y < x"
  show "∃a∈A. y < a"
  proof (rule ccontr)
    assume "¬ (∃a∈A. y < a)"
    then have "cota_superior A y"
      using cota_superior_def by auto
    then show "False"
      using assms es_supremo_def ‹y < x› by auto
  qed
qed

end
</pre>

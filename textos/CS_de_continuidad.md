---
title: Si f es continua en a y el límite de u(n) es a, entonces el límite de f(u(n)) es f(a)
date: 2024-09-04 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

En Lean4, se puede definir que \\(a\\) es el límite de la sucesión \\(u\\) por
<pre lang="lean">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
</pre>
y que f es continua en a por
<pre lang="lean">
   def continua_en (f : ℝ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε
</pre>

Demostrar que si \\(f\\) es continua en \\(a\\) y el límite de \\(u(n)\\) es \\(a\\), entonces el límite de \\(f(u(n))\\) es \\(f(a)\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {f : ℝ → ℝ}
variable {a : ℝ}
variable {u : ℕ → ℝ}

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| ≤ ε

def continua_en (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε

example
  (hf : continua_en f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(ε > 0\\). Tenemos que demostrar que existe un \\(k ∈ ℕ\\) tal que para todo \\(n ≥ k\\),
\\[ |(f ∘ u)(n) - f(a)| ≤ ε \\tag{1} \\]

Puesto que \\(f\\) es continua en \\(a\\), existe un \\(δ > 0\\) tal que
\\[ |x - a| ≤ δ → |f(x) - f(a)| ≤ ε \\tag{2} \\]
Y, puesto que el límite de \\(u(n)\\) es \\(a\\), existe un \\(k ∈ ℕ\\) tal que para todo \\(n ≥ k\\),
\\[ |u(n) - a| ≤ δ \\tag{3} \\]

Para demostrar (1), sea \\(n ∈ ℕ\\) tal que \\(n ≥ k\\). Entonces,
\\begin{align}
   |(f ∘ u)(n) - f(a)| &= |f(u(n)) - f(a)|    \\\\
                       &≤ ε                   &&\\text{[por (2) y (3)]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {f : ℝ → ℝ}
variable {a : ℝ}
variable {u : ℕ → ℝ}

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| ≤ ε

def continua_en (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε

-- 1ª demostración
-- ===============

example
  (hf : continua_en f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  obtain ⟨δ, hδ1, hδ2⟩ := hf ε hε
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  obtain ⟨k, hk⟩ := hu δ hδ1
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  use k
  -- ⊢ ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(f ∘ u) n - f a| ≤ ε
  calc |(f ∘ u) n - f a| = |f (u n) - f a| := by simp only [Function.comp_apply]
                       _ ≤ ε               := hδ2 (u n) (hk n hn)

-- 2ª demostración
-- ===============

example
  (hf : continua_en f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  obtain ⟨δ, hδ1, hδ2⟩ := hf ε hε
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  obtain ⟨k, hk⟩ := hu δ hδ1
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  exact ⟨k, fun n hn ↦ hδ2 (u n) (hk n hn)⟩

-- 3ª demostración
-- ===============

example
  (hf : continua_en f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  rcases hf ε hε with ⟨δ, hδ1, hδ2⟩
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  rcases hu δ hδ1 with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  use k
  -- ⊢ ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(f ∘ u) n - f a| ≤ ε
  apply hδ2
  -- ⊢ |u n - a| ≤ δ
  exact hk n hn

-- 4ª demostración
-- ===============

example
  (hf : continua_en f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  rcases hf ε hε with ⟨δ, hδ1, hδ2⟩
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  rcases hu δ hδ1 with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  exact ⟨k, fun n hn ↦ hδ2 (u n) (hk n hn)⟩

-- Lemas usados
-- ============

-- variable (g : ℝ → ℝ)
-- variable (x : ℝ)
-- #check (Function.comp_apply : (g ∘ f) x = g (f x))
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/CS_de_continuidad.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory CS_de_continuidad
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "limite u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ ≤ ε)"

definition continua_en :: "(real ⇒ real) ⇒ real ⇒ bool" where
  "continua_en f a ⟷
   (∀ε>0. ∃δ>0. ∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"

(* 1ª demostración *)
lemma
  assumes "continua_en f a"
          "limite u a"
  shows "limite (f ∘ u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where hδ1 : "δ > 0" and
                      hδ2 :" (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continua_en_def by auto
  obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) limite_def hδ1 by auto
  have "∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
  proof (intro allI impI)
    fix n
    assume "n ≥ k"
    then have "¦u n - a¦ ≤ δ"
      using hk by auto
    then show "¦(f ∘ u) n - f a¦ ≤ ε"
      using hδ2 by simp
  qed
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    by auto
qed

(* 2ª demostración *)
lemma
  assumes "continua_en f a"
          "limite u a"
  shows "limite (f ∘ u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where hδ1 : "δ > 0" and
                      hδ2 :" (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continua_en_def by auto
  obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) limite_def hδ1 by auto
  have "∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    using hk hδ2 by simp
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    by auto
qed

(* 3ª demostración *)
lemma
  assumes "continua_en f a"
          "limite u a"
  shows "limite (f ∘ u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where hδ1 : "δ > 0" and
                      hδ2 :" (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continua_en_def by auto
  obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) limite_def hδ1 by auto
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    using hk hδ2 by auto
qed

(* 4ª demostración *)
lemma
  assumes "continua_en f a"
          "limite u a"
  shows "limite (f ∘ u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where
              hδ : "δ > 0 ∧ (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continua_en_def by auto
  then obtain k where "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) limite_def by auto
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    using hδ by auto
qed

(* 5ª demostración *)
lemma
  assumes "continua_en f a"
          "limite u a"
  shows "limite (f ∘ u) (f a)"
  using assms continua_en_def limite_def
  by force

end
</pre>

---
title: Si x es límite de u e y es cota superior de u, entonces x ≤ y
date: 2024-09-03 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

En Lean4, se puede definir que \\(a\\) es el límite de la sucesión \\(u\\)
por
<pre lang="haskell">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
</pre>
y que \\(a\\) es una cota superior de \\(u\\) por
<pre lang="haskell">
   def cota_superior (u : ℕ → ℝ) (a : ℝ) :=
     ∀ n, u n ≤ a
</pre>

Demostrar que si \\(x\\) es el límite de la sucesión \\(u\\) e \\(y\\) es una cota superior de \\(u\\), entonces \\(x ≤ y\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable  (u : ℕ → ℝ)
variable (x y : ℝ)

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε

def cota_superior (u : ℕ → ℝ) (a : ℝ) :=
  ∀ n, u n ≤ a

example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Usando como lema la propiedad del ejercicio anterior que afirma que para todo \\(x, y ∈ ℝ\\),
\\[ (∀ ε > 0, y ≤ x + ε) → y ≤ x \\]
la demostración de \\(x ≤ y\\) se reduce a demostrar que
\\[ ∀ ε > 0, x ≤ y + ε \\]
Para demostrarlo, sea \\(ε > 0\\). Entonces, usando que \\(x\\) es el límite de la sucesión \\(u\\), existe un \\(k ∈ ℕ\\) tal que
\\[ ∀ n ≥ k, |u(n) - x| < ε \\]
Luego,
\\[ |u(k) - x| < ε \\]
de donde,
\\[ -ε < u(k) - x \\]
y, reordenando,
\\[ x < u(k) + ε  \\tag{1} \\]
Por otro lado, pouesto que \\(y\\) es una cota superior de \\(u\\), se tiene que
\\[ u(k) < y \\tag{2} \\]
De (1) y (2) se obtiene que
\\[ x < y + ε \\]
que es lo que había que demostrar.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable  (u : ℕ → ℝ)
variable (x y : ℝ)

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε

def cota_superior (u : ℕ → ℝ) (a : ℝ) :=
  ∀ n, u n ≤ a

-- 1º demostración
-- ===============

example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
by
  apply le_of_forall_pos_le_add
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (le_refl k)
  -- hk : |u k - x| < ε
  replace hk : -ε < u k - x := neg_lt_of_abs_lt hk
  replace hk : x < u k + ε := neg_lt_sub_iff_lt_add'.mp hk
  apply le_of_lt
  -- ⊢ x < y + ε
  exact lt_add_of_lt_add_right hk (hy k)

-- 2º demostración
-- ===============

example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
by
  apply le_of_forall_pos_le_add
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (le_refl k)
  -- hk : |u k - x| < ε
  apply le_of_lt
  -- ⊢ x < y + ε
  calc x < u k + ε := neg_lt_sub_iff_lt_add'.mp (neg_lt_of_abs_lt hk)
       _ ≤ y + ε   := add_le_add_right (hy k) ε

-- 3º demostración
-- ===============

example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
by
  apply le_of_forall_pos_le_add
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (by linarith)
  rw [abs_lt] at hk
  -- hk : -ε < u k - x ∧ u k - x < ε
  linarith [hy k]

-- Lemas usados
-- ============

-- variable (n : ℕ)
-- variable (a b c d : ℝ)
-- #check (add_le_add_right : b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)
-- #check (le_of_lt : a < b → a ≤ b)
-- #check (le_refl n : n ≤ n)
-- #check (lt_add_of_lt_add_right : a < b + c → b ≤ d → a < d + c)
-- #check (neg_lt_of_abs_lt : |a| < b → -b < a)
-- #check (neg_lt_sub_iff_lt_add' : -b < a - c ↔ c < a + b)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Los_limites_son_menores_o_iguales_que_las_cotas_superiores.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Los_limites_son_menores_o_iguales_que_las_cotas_superiores
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "limite u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ < ε)"

definition cota_superior :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "cota_superior u c ⟷ (∀n. u n ≤ c)"

(* 1ª demostración *)
lemma
  fixes x y :: real
  assumes "limite u x"
          "cota_superior u y"
  shows   "x ≤ y"
proof (rule field_le_epsilon)
  fix ε :: real
  assume "0 < ε"
  then obtain k where hk : "∀n≥k. ¦u n - x¦ < ε"
    using assms(1) limite_def by auto
  then have "¦u k - x¦ < ε"
    by simp
  then have "-ε < u k - x"
    by simp
  then have "x < u k + ε"
    by simp
  moreover have "u k ≤ y"
    using assms(2) cota_superior_def by simp
  ultimately show "x ≤ y + ε"
    by simp
qed

(* 2ª demostración *)
lemma
  fixes x y :: real
  assumes "limite u x"
          "cota_superior u y"
  shows   "x ≤ y"
proof (rule field_le_epsilon)
  fix ε :: real
  assume "0 < ε"
  then obtain k where hk : "∀n≥k. ¦u n - x¦ < ε"
    using assms(1) limite_def by auto
  then have "x < u k + ε"
    by auto
  moreover have "u k ≤ y"
    using assms(2) cota_superior_def by simp
  ultimately show "x ≤ y + ε"
    by simp
qed

(* 3ª demostración *)
lemma
  fixes x y :: real
  assumes "limite u x"
          "cota_superior u y"
  shows   "x ≤ y"
proof (rule field_le_epsilon)
  fix ε :: real
  assume "0 < ε"
  then obtain k where hk : "∀n≥k. ¦u n - x¦ < ε"
    using assms(1) limite_def by auto
  then show "x ≤ y + ε"
    using assms(2) cota_superior_def
    by (smt (verit) order_refl)
qed

end
</pre>

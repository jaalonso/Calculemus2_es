-- CS_de_continuidad.lean
-- Si f es continua en a y el límite de u(n) es a, entonces el límite de f(u(n)) es f(a)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla,  4-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, se puede definir que a es el límite de la sucesión u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
-- y que f es continua en a por
--    def continua_en (f : ℝ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε
--
-- Demostrar que si f es continua en a y el límite de u(n) es a,
-- entonces el límite de f(u(n)) es f(a).
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε > 0. Tenemos que demostrar que existe un k ∈ ℕ tal que para
-- todo n ≥ k,
--    |(f ∘ u)(n) - f(a)| ≤ ε                                        (1)
--
-- Puesto que f es continua en a, existe un δ > 0 tal que
--    |x - a| ≤ δ → |f(x) - f(a)| ≤ ε                                (2)
-- Y, puesto que el límite de u(n) es a, existe un k ∈ ℕ tal que para
-- todo n ≥ k,
--    |u(n) - a| ≤ δ                                                 (3)
--
-- Para demostrar (1), sea n ∈ ℕ tal que n ≥ k. Entonces,
--    |(f ∘ u)(n) - f(a)| = |f(u(n)) - f(a)|
--                        ≤ ε                   [por (2) y (3)]

-- Demostraciones con Lean4
-- ========================

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

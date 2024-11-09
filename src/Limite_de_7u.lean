-- Limite_de_7u.lean
-- Si el límite de u(n) es a, entonces el de 7u(n) es 7a.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-noviembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--      fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
--
-- Demostrar que que si el límite de uₙ es a, entonces el de
-- 7uₙ es 7a.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε > 0. Tenemos que demostrar que, existe un N ∈ ℕ tal que
--    (∀ n ∈ ℕ)[N ≤ n → |7u(n) - 7a| < ε]                          (1)
-- Puesto que el límite de u(n) es a, existe un N ∈ ℕ tal que
--    (∀ n ∈ ℕ)[N ≤ n → |u(n) - a| < ε/7]                              (2)
-- Sea N ∈ ℕ que verifica (2), veamos que el mismo N verifica (1). Para
-- ello, sea n ∈ ℕ tal que N ≤ n. Entonces,
--    |7u(n) - 7a| = |7(u(n) - a)|
--                   = |7||u(n) - a|
--                   = 7|u(n) - a|
--                   < 7(ε / 7)        [por (2)]
--                   = ε

-- Demostraciones con Lean4
-- ========================

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

-- Limite_multiplicado_por_una_constante_2.lean
-- Si el límite de la sucesión uₙ es a y c ∈ ℝ, entonces el límite de cuₙ es ca
-- José A. Alonso Jiménez
-- Sevilla, 29 de noviembre de 2024
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
-- uₙc es ac.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En un [ejercicio anterior](https://tinyurl.com/2244qcxs) se han
-- presentado demostraciones de la siguiente propiedad
--    "Si el límite de la sucesión uₙ es a y c ∈ ℝ, entonces el límite
--    de cuₙ es ca."
--
-- A partir de dicha propiedad se demuestra que
--    "Si el límite de la sucesión uₙ es a y c ∈ ℝ, entonces el límite
--    de uₙc es ac."
-- En efecto, supongamos que
--    el límite de uₙ es a
-- Entonces, por la propiedad anterior,
--    el límite de cuₙ es ca                                         (1)
-- Pero, por la conmutatividad del producto, se tiene que
--    (∀n ∈ ℕ)[cuₙ = uₙc]                                            (2)
--    ca = ac                                                        (3)
-- Por (1), (2) y (3) se tiene que
--    el límite de uₙc es ac

-- Demostraciones con Lean4
-- ========================

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

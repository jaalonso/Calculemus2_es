-- CS_de_y_le_x.lean
-- Si (∀ ε > 0, y ≤ x + ε), entonces y ≤ x
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean x, y ∈ ℝ. Demostrar que
--    (∀ ε > 0, y ≤ x + ε) → y ≤ x
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sean x, y ∈ ℝ tales que
--    (∀ ε > 0)[y ≤ x + ε]                                           (1)
-- Demostraremos, por reducción al absurdo, que y ≤ x. Para ello,
-- supongamos que
--    x < y                                                          (2)
-- Entonces,
--   (y - x)/2 > 0
-- y, por (1),
--   y ≤ x + (y - x)/2
-- Luego,
--   2y ≤ 2x + (y - x)
-- y, simplificando,
--   y ≤ x
-- que es una contracción con (2).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {x y : ℝ}

-- 1ª demostración
-- ===============

example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
by
  intro h
  -- h : ∀ ε > 0, y ≤ x + ε
  -- ⊢ y ≤ x
  by_contra! h1
  -- h1 : x < y
  -- ⊢ False
  have h2 : (y - x)/2 > 0           := by linarith
  have    : y ≤ x + (y - x)/2       := h ((y - x) / 2) h2
  have    : 2 * y ≤ 2 * x + (y - x) := by linarith
  have    : y ≤ x                   := by linarith
  have h3 : ¬x < y                  := by linarith
  exact h3 h1

-- 2ª demostración
-- ===============

example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
by
  contrapose!
  -- ⊢ x < y → ∃ ε > 0, x + ε < y
  intro h
  -- h : x < y
  -- ⊢ ∃ ε > 0, x + ε < y
  use (y-x)/2
  -- ⊢ (y - x) / 2 > 0 ∧ x + (y - x) / 2 < y
  constructor
  . -- ⊢ (y - x) / 2 > 0
    apply half_pos
    -- ⊢ 0 < y - x
    exact sub_pos.mpr h
  . -- ⊢ x + (y - x) / 2 < y
    calc x + (y - x) / 2
         = (x + y) / 2
              := by ring_nf
       _ < (y + y) / 2
              := div_lt_div_of_pos_right (add_lt_add_right h y)
                                         zero_lt_two
       _ = (2 * y) / 2
              := congrArg (. / 2) (two_mul y).symm
       _ = y
              := mul_div_cancel_left₀ y (NeZero.ne' 2).symm

-- 3ª demostración
-- ===============

example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
by
  contrapose!
  -- ⊢ x < y → ∃ ε > 0, x + ε < y
  intro h
  -- h : x < y
  -- ⊢ ∃ ε > 0, x + ε < y
  use (y-x)/2
  -- ⊢ (y - x) / 2 > 0 ∧ x + (y - x) / 2 < y
  constructor
  . -- ⊢ (y - x) / 2 > 0
    exact half_pos (sub_pos.mpr h)
  . calc x + (y - x) / 2
         = (x + y) / 2   := by ring_nf
       _ < (y + y) / 2   := by linarith
       _ = (2 * y) / 2   := by ring_nf
       _ = y             := by ring_nf

-- 4ª demostración
-- ===============

example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
by
  contrapose!
  -- ⊢ x < y → ∃ ε > 0, x + ε < y
  intro h
  -- h : x < y
  -- ⊢ ∃ ε > 0, x + ε < y
  use (y-x)/2
  -- ⊢ (y - x) / 2 > 0 ∧ x + (y - x) / 2 < y
  constructor
  . -- ⊢ (y - x) / 2 > 0
    apply half_pos
    -- ⊢ 0 < y - x
    exact sub_pos.mpr h
  . -- ⊢ x + (y - x) / 2 < y
    exact add_sub_div_two_lt h

-- 5ª demostración
-- ===============

example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
by
  contrapose!
  -- ⊢ x < y → ∃ ε > 0, x + ε < y
  intro h
  -- h : x < y
  -- ⊢ ∃ ε > 0, x + ε < y
  use (y-x)/2
  -- ⊢ (y - x) / 2 > 0 ∧ x + (y - x) / 2 < y
  constructor
  . -- ⊢ (y - x) / 2 > 0
    field_simp [h]
  . -- ⊢ x + (y - x) / 2 < y
    exact add_sub_div_two_lt h

-- 6ª demostración
-- ===============

example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
by
  contrapose!
  -- ⊢ x < y → ∃ ε > 0, x + ε < y
  intro h
  -- h : x < y
  -- ⊢ ∃ ε > 0, x + ε < y
  use (y-x)/2
  -- ⊢ (y - x) / 2 > 0 ∧ x + (y - x) / 2 < y
  constructor
  . -- ⊢ (y - x) / 2 > 0
    linarith
  . -- ⊢ x + (y - x) / 2 < y
    linarith

-- 7ª demostración
-- ===============

example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
by
  contrapose!
  -- ⊢ x < y → ∃ ε > 0, x + ε < y
  intro h
  -- h : x < y
  -- ⊢ ∃ ε > 0, x + ε < y
  use (y-x)/2
  -- ⊢ (y - x) / 2 > 0 ∧ x + (y - x) / 2 < y
  constructor <;> linarith

-- 8ª demostración
-- ===============

example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
by
  intro h1
  -- h1 : ∀ ε > 0, y ≤ x + ε
  -- ⊢ y ≤ x
  by_contra h2
  -- h2 : ¬y ≤ x
  -- ⊢ False
  replace h2 : x < y := not_le.mp h2
  rcases (exists_between h2) with ⟨z, h3, h4⟩
  -- z : ℝ
  -- h3 : x < z
  -- h4 : z < y
  replace h3 : 0 < z - x := sub_pos.mpr h3
  replace h1 : y ≤ x + (z - x) := h1 (z - x) h3
  replace h1 : y ≤ z := by linarith
  have h4 : y < y := gt_of_gt_of_ge h4 h1
  exact absurd h4 (irrefl y)

-- 9ª demostración
-- ===============

example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
by
  intro h1
  -- h1 : ∀ ε > 0, y ≤ x + ε
  -- ⊢ y ≤ x
  by_contra h2
  -- h2 : ¬y ≤ x
  -- ⊢ False
  replace h2 : x < y := not_le.mp h2
  -- h2 : x < y
  rcases (exists_between h2) with ⟨z, hxz, hzy⟩
  -- z : ℝ
  -- hxz : x < z
  -- hzy : z < y
  apply lt_irrefl y
  -- ⊢ y < y
  calc y ≤ x + (z - x) := h1 (z - x) (sub_pos.mpr hxz)
       _ = z           := by ring
       _ < y           := hzy

-- 10ª demostración
-- ===============

example :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
le_of_forall_pos_le_add

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- variable (p q : Prop)
-- #check (absurd : p → ¬p → q)
-- #check (add_lt_add_right : b < c → ∀ (a : ℝ), b + a < c + a)
-- #check (add_sub_div_two_lt: a < b → a + (b - a) / 2 < b)
-- #check (div_lt_div_of_pos_right : a < b → 0 < c → a / c < b / c)
-- #check (exists_between : a < b → ∃ c, a < c ∧ c < b)
-- #check (gt_of_gt_of_ge : a > b → b ≥ c → a > c)
-- #check (half_pos : 0 < a → 0 < a / 2)
-- #check (irrefl a : ¬a < a)
-- #check (le_of_forall_pos_le_add : (∀ ε > 0, y ≤ x + ε) → y ≤ x)
-- #check (lt_irrefl a : ¬a < a)
-- #check (mul_div_cancel_left₀ b : a ≠ 0 → a * b / a = b)
-- #check (not_le : ¬a ≤ b ↔ b < a)
-- #check (sub_pos : 0 < a - b ↔ b < a)
-- #check (two_mul a : 2 * a = a + a)
-- #check (zero_lt_two : 0 < 2)

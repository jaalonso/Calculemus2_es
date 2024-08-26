-- Producto_constante_no_nula_es_inyectiva.lean
-- Si c ≠ 0, entonces la función (x ↦ cx) es inyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que para todo c distinto de cero la función
--    f(x) = c * x
-- es inyectiva
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el lema
--    (∀ a, b, c) [a ≠ 0 → (a * b = a * c ↔ b = c))]             (L1)
-- Hay que demostrar que
--    (∀ x₁, x₂) [f(x₁) = f(x₂) → x₁ = x₂]
-- Sean x₁, x₂ tales que f(x₁) = f(x₂). Entonces,
--    cx₁ = cx₂
-- y, por L1 y puesto que c ≠ 0, se tiene que
--    x₁ = x₂.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
open Function
variable {c : ℝ}

-- 1ª demostración
example
  (h : c ≠ 0)
  : Injective ((c * .)) :=
by
  intro (x1 : ℝ) (x2 : ℝ) (h1 : c * x1 = c * x2)
  show x1 = x2
  exact (mul_right_inj' h).mp h1

-- 2ª demostración
example
  (h : c ≠ 0)
  : Injective ((c * .)) :=
fun _ _ h1 ↦ mul_left_cancel₀ h h1

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (mul_right_inj' : a ≠ 0 → (a * b = a * c ↔ b = c))
-- #check (mul_left_cancel₀ : a ≠ 0 → a * b = a * c → b = c)

-- Identidad_de_Brahmagupta-Fibonacci.lean
-- Identidad de Brahmagupta-Fibonacci
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar la identidad de Brahmagupta-Fibonacci https://is.gd/9PJ56H
--    (a² + b²) * (c² + d²) = (ac - bd)² + (ad + bc)²
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se demuestra por la siguiente cadena de igualdades
--    (a^2 + b^2)(c^2 + d^2) = a^2(c^2 + d^2) + b^2(c^2 + d^2)
--                           = (a^2*c^2 + a^2d^2) + b^2(c^2 + d^2)
--                           = (a^2c^2 + a^2d^2) + (b^2c^2 + b^2d^2)
--                           = ((ac)^2 + (bd)^2) + ((ad)^2 + (bc)^2)
--                           = ((a*c)^2 - 2acbd + (bd)^2) + ((ad)^2 + 2adbc + (bc)^2)
--                           = (ac - bd)^2 + (ad + bc)^2

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c d : ℝ)

-- 1ª demostración
-- ===============

example : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
calc (a^2 + b^2) * (c^2 + d^2)
     = a^2 * (c^2 + d^2) + b^2 * (c^2 + d^2)
         := right_distrib (a^2) (b^2) (c^2 + d^2)
   _ = (a^2*c^2 + a^2*d^2) + b^2 * (c^2 + d^2)
         := congr_arg₂ (. + .) (left_distrib (a^2) (c^2) (d^2)) rfl
   _ = (a^2*c^2 + a^2*d^2) + (b^2*c^2 + b^2*d^2)
         := congr_arg₂ (. + .) rfl (left_distrib (b^2) (c^2) (d^2))
   _ = ((a*c)^2 + (b*d)^2) + ((a*d)^2 + (b*c)^2)
         := by ring
   _ = ((a*c)^2 - 2*a*c*b*d + (b*d)^2) + ((a*d)^2 + 2*a*d*b*c + (b*c)^2)
         := by ring
   _ = (a*c - b*d)^2 + (a*d + b*c)^2
         := by ring

-- 2ª demostración
-- ===============

example : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
by ring

-- Lemas usados
-- ============

-- variable (f : ℝ → ℝ → ℝ)
-- variable (x x' y y' : ℝ)
-- #check (congr_arg₂ f : x = x' → y = y' → f x y = f x' y')
-- #check (left_distrib a b c : a * (b + c) = a * b + a * c)
-- #check (right_distrib a b c: (a + b) * c = a * c + b * c)

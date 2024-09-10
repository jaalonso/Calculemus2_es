-- Suma_de_los_primeros_cubos.lean
-- Pruebas de 0³+1³+2³+3³+···+n³ = (n(n+1)/2)²
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de los primeros cubos
--    0³ + 1³ + 2³ + 3³ + ··· + n³
-- es (n(n+1)/2)²
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea
--    s(n) = 0³ + 1³ + 2³ + 3³ + ··· + n³
-- Tenemos que demostrar que
--    s(n) = (n(n+1)/2)²
-- o, equivalentemente que
--    4s(n) = (n(n+1))²
-- Lo haremos por inducción sobre n.
--
-- Caso base: Sea n = 0. Entonces,
--    4s(n) = 4s(0)
--          = 4·0
--          = 0
--          = (0(0 + 1))^2
--          = (n(n + 1))^2
--
-- Paso de inducción: Sea n = m+1 y supongamos la hipótesis de inducción
-- (HI)
--    4s(m) = (m(m + 1))^2
-- Entonces,
--    4s(n) = 4s(m+1)
--          = 4(s(m) + (m+1)^3)
--          = 4s(m) + 4(m+1)^3
--          = (m*(m+1))^2 + 4(m+1)^3        [por HI]
--          = (m+1)^2*(m^2+4m+4)
--          = (m+1)^2*(m+2)^2
--          = ((m+1)(m+2))^2
--          = ((m+1)(m+1+1))^2

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)

set_option pp.fieldNotation false

@[simp]
def sumaCubos : ℕ → ℕ
  | 0   => 0
  | n+1 => sumaCubos n + (n+1)^3

-- 1ª demostración
-- ===============

example :
  4 * sumaCubos n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    -- ⊢ 4 * sumaCubos 0 = (0 * (0 + 1)) ^ 2
    calc 4 * sumaCubos 0
         = 4 * 0             := by simp only [sumaCubos]
       _ = (0 * (0 + 1)) ^ 2 := by simp
  | succ m HI =>
     -- m : ℕ
     -- HI : 4 * sumaCubos m = (m * (m + 1)) ^ 2
     -- ⊢ 4 * sumaCubos (m + 1) = ((m + 1) * (m + 1 + 1)) ^ 2
    calc 4 * sumaCubos (m + 1)
         = 4 * (sumaCubos m + (m+1)^3)
           := by simp only [sumaCubos]
       _ = 4 * sumaCubos m + 4*(m+1)^3
           := by ring
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) HI
       _ = (m+1)^2*(m^2+4*m+4)
           := by ring
       _ = (m+1)^2*(m+2)^2
           := by ring
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1))^2
           := by simp

-- 2ª demostración
-- ===============

example :
  4 * sumaCubos n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    simp
  | succ m HI =>
    calc 4 * sumaCubos (m+1)
         = 4 * sumaCubos m + 4*(m+1)^3
           := by {simp ; ring_nf}
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) HI
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1)) ^ 2
           := by simp

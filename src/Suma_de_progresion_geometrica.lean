-- Suma_de_progresion_geometrica.lean
-- Pruebas de a+aq+aq²+···+aqⁿ = a(1-qⁿ⁺¹)/(1-q)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla,  8-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si q ≠ 1, entonces la suma de los términos de la
-- progresión geométrica
--    a + aq + aq² + ··· + aqⁿ
-- es
--      a(1 - qⁿ⁺¹)
--    --------------
--        1 - q
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea
--    s(a,q,n) = a + aq + aq² + ··· + aqⁿ
-- Tenemos que demostrar que
--    s(a,q,n) = a(1 - qⁿ⁺¹)/(1 - q)
-- o, equivalentemente que
--    (1 - q)s(a,q,n) = a(1 - qⁿ⁺¹)
-- Lo haremos por inducción sobre n.
--
-- Caso base: Sea n = 0. Entonces,
--    (1 - q)s(a,q,n) = (1 - q)s(a, q, 0)
--                    = (1 - q)a
--                    = a(1 - q^(0 + 1))
--                    = a(1 - q^(n + 1))
--
-- Paso de inducción: Sea n = m+1 y supongamos la hipótesis de inducción
-- (HI)
--    (1 - q)s(a,q,m) = a(1 - q^(n + 1))
-- Entonces,
--    (1 - q)s(a,q,n)
--    = (1 - q)s(a,q,m+1)
--    = (1 - q)(s(a,q,m) + aq^(m + 1))
--    = (1 - q)s(a,q,m) + (1 - q)aq^(m + 1)
--    = a(1 - q^(m + 1)) + (1 - q)aq^(m + 1)   [por HI]
--    = a(1 - q^(m + 1 + 1))
--    = a(1 - q^(n + 1))

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a q : ℝ)

set_option pp.fieldNotation false

@[simp]
def sumaPG : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, q, n + 1 => sumaPG a q n + (a * q^(n + 1))

-- 1ª demostración
-- ===============

example
  (h : q ≠ 1)
  : sumaPG a q n = a * (1 - q^(n + 1)) / (1 - q) :=
by
  have h1 : 1 - q ≠ 0 := by exact sub_ne_zero_of_ne (id (Ne.symm h))
  suffices h : (1 - q) * sumaPG a q n = a * (1 - q ^ (n + 1))
    from by exact CancelDenoms.cancel_factors_eq_div h h1
  induction n with
  | zero =>
    -- ⊢ (1 - q) * sumaPG a q 0 = a * (1 - q ^ (0 + 1))
    calc (1 - q) * sumaPG a q 0
         = (1 - q) * a           := by simp only [sumaPG]
       _ = a * (1 - q)           := by simp only [mul_comm]
       _ = a * (1 - q ^ 1)       := by simp
       _ = a * (1 - q ^ (0 + 1)) := by simp
  | succ m HI =>
    -- m : ℕ
    -- HI : (1 - q) * sumaPG a q m = a * (1 - q ^ (m + 1))
    -- ⊢ (1 - q) * sumaPG a q (m + 1) = a * (1 - q ^ (m + 1 + 1))
    calc (1 - q) * sumaPG a q (m + 1)
         = (1 - q) * (sumaPG a q m + (a * q^(m + 1)))
           := by simp only [sumaPG]
       _ = (1 - q) * sumaPG a q m + (1 - q) * (a * q ^ (m + 1))
           := by rw [left_distrib]
       _ = a * (1 - q ^ (m + 1)) + (1 - q) * (a * q ^ (m + 1))
           := congrArg  (. + (1 - q) * (a * q ^ (m + 1))) HI
       _ = a * (1 - q ^ (m + 1 + 1))
           := by ring_nf

-- 2ª demostración
-- ===============

example
  (h : q ≠ 1)
  : sumaPG a q n = a * (1 - q^(n + 1)) / (1 - q) :=
by
  have h1 : 1 - q ≠ 0 := by exact sub_ne_zero_of_ne (id (Ne.symm h))
  suffices h : (1 - q) * sumaPG a q n = a * (1 - q ^ (n + 1))
    from by exact CancelDenoms.cancel_factors_eq_div h h1
  induction n with
  | zero =>
    -- ⊢ (1 - q) * sumaPG a q 0 = a * (1 - q ^ (0 + 1))
    simp
    -- ⊢ (1 - q) * a = a * (1 - q)
    ring_nf
  | succ m HI =>
    -- m : ℕ
    -- HI : (1 - q) * sumaPG a q m = a * (1 - q ^ (m + 1))
    -- ⊢ (1 - q) * sumaPG a q (m + 1) = a * (1 - q ^ (m + 1 + 1))
    calc (1 - q) * sumaPG a q (m + 1)
         = (1 - q) * (sumaPG a q m + (a * q ^ (m + 1)))
           := rfl
       _ = (1 - q) * sumaPG a q m + (1 - q) * (a * q ^ (m + 1))
           := by ring_nf
       _ = a * (1 - q ^ (m + 1)) + (1 - q) * (a * q ^ (m + 1))
           := congrArg  (. + (1 - q) * (a * q ^ (m + 1))) HI
       _ = a * (1 - q ^ (m + 1 + 1))
           := by ring_nf

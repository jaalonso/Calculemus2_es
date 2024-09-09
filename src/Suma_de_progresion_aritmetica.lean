-- Suma_de_progresion_aritmetica.lean
-- Pruebas de a+(a+d)+(a+2d)+···+(a+nd)=(n+1)(2a+nd)/2
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de los términos de la progresión aritmética
--    a + (a + d) + (a + 2 × d) + ··· + (a + n × d)
-- es (n + 1) × (2 × a + n × d) / 2.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea
--    s(a,d,n) = a + (a + d) + (a + 2d) + ··· + (a + nd)
-- Tenemos que demostrar que
--    s(a,d,n) = (n + 1)(2a + nd) / 2
-- o, equivalentemente que
--    2s(a,d,n) = (n + 1)(2a + nd)
-- Lo haremos por inducción sobre n.
--
-- Caso base: Sea n = 0. Entonces,
--    2s(a,d,n) = 2s(a,d,0)
--              = 2·a
--              = (0 + 1)(2a + 0.d)
--              = (n + 1)(2a + nd)
--
-- Paso de indución: Sea n = m+1 y supongamos la hipótesis de inducción
-- (HI)
--    2s(a,d,m) = (m + 1)(2a + md)
-- Entonces,
--    2s(a,d,n) = 2s(a,d,m+1)
--              = 2(s(a,d,m) + (a + (m + 1)d))
--              = 2s(a,d,m) + 2(a + (m + 1)d)
--              = ((m + 1)(2a + md)) + 2(a + (m + 1)d) [por HI]
--              = (m + 2)(2a + (m + 1)d)
--              = (n + 1)(2a + nd)

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a d : ℝ)

set_option pp.fieldNotation false

def sumaPA : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, d, n + 1 => sumaPA a d n + (a + (n + 1) * d)

@[simp]
lemma sumaPA_zero :
  sumaPA a d 0 = a :=
by simp only [sumaPA]

@[simp]
lemma sumaPA_succ :
  sumaPA a d (n + 1) = sumaPA a d n + (a + (n + 1) * d) :=
by simp only [sumaPA]

-- 1ª demostración
-- ===============

example :
  2 * sumaPA a d n = (n + 1) * (2 * a + n * d) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sumaPA a d 0 = (↑0 + 1) * (2 * a + ↑0 * d)
    have h : 2 * sumaPA a d 0 = (0 + 1) * (2 * a + 0 * d) :=
      calc 2 * sumaPA a d 0
           = 2 * a
               := congrArg (2 * .) (sumaPA_zero a d)
         _ = (0 + 1) * (2 * a + 0 * d)
               := by ring_nf
    exact_mod_cast h
  | succ m HI =>
    -- m : ℕ
    -- HI : 2 * sumaPA a d m = (↑m + 1) * (2 * a + ↑m * d)
    -- ⊢ 2 * sumaPA a d (m + 1) = (↑(m + 1) + 1) * (2 * a + ↑(m + 1) * d)
    calc 2 * sumaPA a d (succ m)
         = 2 * (sumaPA a d m + (a + (m + 1) * d))
           := congrArg (2 * .) (sumaPA_succ m a d)
       _ = 2 * sumaPA a d m + 2 * (a + (m + 1) * d)
           := by ring_nf
       _ = ((m + 1) * (2 * a + m * d)) + 2 * (a + (m + 1) * d)
           := congrArg (. + 2 * (a + (m + 1) * d)) HI
       _ = (m + 2) * (2 * a + (m + 1) * d)
           := by ring_nf
       _ = (succ m + 1) * (2 * a + succ m * d)
           := by norm_cast

-- 2ª demostración
-- ===============

example :
  2 * sumaPA a d n = (n + 1) * (2 * a + n * d) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sumaPA a d 0 = (↑0 + 1) * (2 * a + ↑0 * d)
    simp
  | succ m HI =>
    -- m : ℕ
    -- HI : 2 * sumaPA a d m = (↑m + 1) * (2 * a + ↑m * d)
    -- ⊢ 2 * sumaPA a d (m + 1) = (↑(m + 1) + 1) * (2 * a + ↑(m + 1) * d)
    calc 2 * sumaPA a d (succ m)
         = 2 * (sumaPA a d m + (a + (m + 1) * d))
           := rfl
       _ = 2 * sumaPA a d m + 2 * (a + (m + 1) * d)
           := by ring_nf
       _ = ((m + 1) * (2 * a + m * d)) + 2 * (a + (m + 1) * d)
           := congrArg (. + 2 * (a + (m + 1) * d)) HI
       _ = (m + 2) * (2 * a + (m + 1) * d)
           := by ring_nf
       _ = (succ m + 1) * (2 * a + succ m * d)
           := by norm_cast

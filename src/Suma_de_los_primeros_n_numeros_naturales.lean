-- Suma_de_los_primeros_n_numeros_naturales.lean
-- Pruebas de "0 + 1 + 2 + 3 + ··· + n = n × (n + 1)/2"
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla,  5-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de los números naturales
--    0 + 1 + 2 + 3 + ··· + n
-- es n × (n + 1)/2
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea
--    s(n) = 0 + 1 + 2 + 3 + ··· + n
-- Tenemos que demostrar que
--    s(n) = n(n + 1)/2
-- o, equivalentemente que
--    2s(n) = n(n + 1)
-- Lo haremos por inducción sobre n.
--
-- Caso base: Sea n = 0. Entonces,
--    2s(n) = 2s(0)
--          = 2·0
--          = 0
--          = 0.(0 + 1)
--          = n.(n + 1)
--
-- Paso de indución: Sea n = m+1 y supongamos la hipótesis de inducción
-- (HI)
--    2s(m) = m
-- Entonces,
--    2s(n) = 2s(m+1)
--          = 2(s(m) + (m+1))
--          = 2s(m) + 2(m+1)
--          = m(m + 1) + 2(m + 1)    [por HI]
--          = (m + 2)(m + 1)
--          = (m + 1)(m + 2)
--          = n(n+1)

-- Demostraciones con Lean4
-- ========================

import Init.Data.Nat.Basic
import Mathlib.Tactic

open Nat

variable (n : Nat)

set_option pp.fieldNotation false

def suma : Nat → Nat
  | 0      => 0
  | succ n => suma n + (n+1)

@[simp]
lemma suma_zero : suma 0 = 0 := rfl

@[simp]
lemma suma_succ : suma (n + 1) = suma n + (n+1) := rfl

-- 1ª demostración
-- ===============

example :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * suma 0 = 0 * (0 + 1)
    calc 2 * suma 0
         = 2 * 0       := congrArg (2 * .) suma_zero
       _ = 0           := mul_zero 2
       _ = 0 * (0 + 1) := zero_mul (0 + 1)
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * suma n = n * (n + 1)
    -- ⊢ 2 * suma (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    := congrArg (2 * .) (suma_succ n)
       _ = 2 * suma n + 2 * (n + 1)  := mul_add 2 (suma n) (n + 1)
       _ = n * (n + 1) + 2 * (n + 1) := congrArg (. + 2 * (n + 1)) HI
       _ = (n + 2) * (n + 1)         := (add_mul n 2 (n + 1)).symm
       _ = (n + 1) * (n + 2)         := mul_comm (n + 2) (n + 1)

-- 2ª demostración
-- ===============

example :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * suma 0 = 0 * (0 + 1)
    calc 2 * suma 0
         = 2 * 0       := rfl
       _ = 0           := rfl
       _ = 0 * (0 + 1) := rfl
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * suma n = n * (n + 1)
    -- ⊢ 2 * suma (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    := rfl
       _ = 2 * suma n + 2 * (n + 1)  := by ring
       _ = n * (n + 1) + 2 * (n + 1) := by simp [HI]
       _ = (n + 2) * (n + 1)         := by ring
       _ = (n + 1) * (n + 2)         := by ring

-- 3ª demostración
-- ===============

example :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * suma 0 = 0 * (0 + 1)
    rfl
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * suma n = n * (n + 1)
    -- ⊢ 2 * suma (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    := rfl
       _ = 2 * suma n + 2 * (n + 1)  := by ring
       _ = n * (n + 1) + 2 * (n + 1) := by simp [HI]
       _ = (n + 1) * (n + 2)         := by ring

-- 4ª demostración
-- ===============

example :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero => rfl
  | succ n HI => unfold suma ; linarith [HI]

-- Lemas usados
-- ============

-- variable (a b c : ℕ)
-- #check (add_mul a b c : (a + b) * c = a * c + b * c)
-- #check (mul_add a b c : a * (b + c) = a * b + a * c)
-- #check (mul_comm a b : a * b = b * a)
-- #check (mul_zero a : a * 0 = 0)
-- #check (zero_mul a : 0 * a = 0)

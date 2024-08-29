-- Fibonacci.lean
-- Pruebas de equivalencia de definiciones de la función de Fibonacci.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-agosto-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, se puede definir la función de Fibonacci por
--    def fibonacci : Nat → Nat
--      | 0     => 0
--      | 1     => 1
--      | n + 2 => fibonacci n + fibonacci (n+1)
--
-- Otra definición más eficiente es
--    def fib (n : Nat) : Nat :=
--      (aux n).1
--    where
--      aux : Nat → Nat × Nat
--        | 0   => (0, 1)
--        | n + 1 =>
--          let p := aux n
--          (p.2, p.1 + p.2)
--
-- Demostrar que ambas definiciones son equivalentes; es decir,
--    fibonacci = fib
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración usaremos el siguiente lema auxiliar
--    fib_suma (n : Nat) : fib (n + 2) = fib n + fib (n + 1)
--
-- Tenemos que demostrar que, para todo n ∈ ℕ,
--    fibonacci n = fib n
-- Lo probaremos por inducción en n.
--
-- Caso 1: Supongamos que n = 0. Entonces,
--    fibonacci n = fibonacci 0
--                = 1
-- y
--    fib n = fib 0
--          = (aux 0).1
--          = (0, 1).1
--          = 1
-- Por tanto,
--     fibonacci n = fib n
--
-- Caso 2: Supongamos que n = 1. Entonces,
--    fibonacci n = 1
-- y
--    fib 1 = (aux 1).1
--          = (p.2, p.1 + p.2).1
--            donde p = aux 0
--          = ((0, 1).2, (0, 1).1 + (0, 1).2).1
--          = (1, 0 + 1).1
--          = 1
--
-- Caso 3: Supongamos que n = m + 2 y que se verifica las hipótesis de
-- inducción,
--    HI1 : fibonacci n = fib n
--    HI2 : fibonacci (n + 1) = fib (n + 1)
-- Entonces,
--    fibonacci n
--    = fibonacci (m + 2)
--    = fibonacci m + fibonacci (m + 1)
--    = fib m + fib (m + 1)                [por HI1, HI2]
--    = fib (m + 2)                        [por fib_suma]
--    = fib n

-- Demostraciones con Lean4
-- ========================

open Nat

-- Para que no use la notación con puntos
set_option pp.fieldNotation false

def fibonacci : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibonacci n + fibonacci (n+1)

def fib (n : Nat) : Nat :=
  (aux n).1
where
  aux : Nat → Nat × Nat
    | 0   => (0, 1)
    | n + 1 =>
      let p := aux n
      (p.2, p.1 + p.2)

-- Lema auxiliar
-- =============

theorem fib_suma (n : Nat) : fib (n + 2) = fib n + fib (n + 1) :=
by rfl

-- 1ª demostración
-- ===============

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n HI1 HI2 =>
    -- n : Nat
    -- HI1 : fibonacci n = fib n
    -- HI2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    rw [fib_suma]
    -- ⊢ fibonacci (succ (succ n)) = fib n + fib (n + 1)
    rw [fibonacci]
    -- ⊢ fibonacci n + fibonacci (n + 1) = fib n + fib (n + 1)
    rw [HI1]
    -- ⊢ fib n + fibonacci (n + 1) = fib n + fib (n + 1)
    rw [HI2]

-- 2ª demostración
-- ===============

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n HI1 HI2 =>
    -- n : Nat
    -- HI1 : fibonacci n = fib n
    -- HI2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    calc fibonacci (succ (succ n))
         = fibonacci n + fibonacci (n + 1) := by rw [fibonacci]
       _ = fib n + fib (n + 1)             := by rw [HI1, HI2]
       _ = fib (succ (succ n))             := by rw [fib_suma]

-- 3ª demostración
-- ===============

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n HI1 HI2 =>
    -- n : Nat
    -- HI1 : fibonacci n = fib n
    -- HI2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    simp [HI1, HI2, fibonacci, fib_suma]

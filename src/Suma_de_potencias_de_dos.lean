-- Suma_de_potencias_de_dos.lean
-- Pruebas de ∑k<n. 2^k = 2^n-1
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    1 + 2 + 2² + 2³ + ... + 2⁽ⁿ⁻¹⁾ = 2ⁿ - 1
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por indución en n.
--
-- Caso base: Sea n = 0. Entonces,
--    ∑k<0. 2^k = 0
--              = 2^0 - 1
--              = 2^n - 1
--
-- Paso de inducción: Sea n = m+1 y supongamos la hipótesis de inducción
--(HI)
--    ∑k<m. 2^k = 2^m-1
-- Entonces,
--    ∑k<n. 2^k = ∑k<(m+1). 2^k
--              = ∑k<m. 2^k + 2^m
--              = (2^m - 1) + 2^m    [por HI]
--              = (2^m + 2^m) - 1
--              = 2^(m + 1) - 1
--              = 2^n - 1

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

open Finset Nat

variable (n : ℕ)

-- 1ª demostración
-- ===============

example :
  ∑ k in range n, 2^k = 2^n - 1 :=
by
  induction n with
  | zero =>
    -- ⊢ ∑ k ∈ range 0, 2 ^ k = 2 ^ 0 - 1
    calc ∑ k ∈ range 0, 2 ^ k
         = 0                   := sum_range_zero (2 ^ .)
       _ = 2 ^ 0 - 1           := by omega
  | succ m HI =>
    -- m : ℕ
    -- HI : ∑ k ∈ range m, 2 ^ k = 2 ^ m - 1
    -- ⊢ ∑ k ∈ range (m + 1), 2 ^ k = 2 ^ (m + 1) - 1
    have h1 : (2^m - 1) + 2^m = (2^m + 2^m) - 1 := by
      have h2 : 2^m ≥ 1 := Nat.one_le_two_pow
      omega
    calc ∑ k in range (m + 1), 2^k
       = ∑ k in range m, (2^k) + 2^m
           := sum_range_succ (2 ^ .) m
     _ = (2^m - 1) + 2^m
           := congrArg (. + 2^m) HI
     _ = (2^m + 2^m) - 1
           := h1
     _ = 2^(m + 1) - 1
           := congrArg (. - 1) (two_pow_succ m).symm

-- 2ª demostración
-- ===============

example :
  ∑ k in range n, 2^k = 2^n - 1 :=
by
  induction n with
  | zero =>
    -- ⊢ ∑ k ∈ range 0, 2 ^ k = 2 ^ 0 - 1
    simp
  | succ m HI =>
    -- m : ℕ
    -- HI : ∑ k ∈ range m, 2 ^ k = 2 ^ m - 1
    -- ⊢ ∑ k ∈ range (m + 1), 2 ^ k = 2 ^ (m + 1) - 1
    have h1 : (2^m - 1) + 2^m = (2^m + 2^m) - 1 := by
      have h2 : 2^m ≥ 1 := Nat.one_le_two_pow
      omega
    calc ∑ k in range (m + 1), 2^k
       = ∑ k in range m, (2^k) + 2^m := sum_range_succ (2 ^ .) m
     _ = (2^m - 1) + 2^m             := by linarith
     _ = (2^m + 2^m) - 1             := h1
     _ = 2^(m + 1) - 1               := by omega

-- Lemas usados
-- ============

-- variable (f : ℕ → ℕ)
-- #check (Nat.one_le_two_pow : 1 ≤ 2 ^ n)
-- #check (Nat.two_pow_succ n : 2 ^ (n + 1) = 2 ^ n + 2 ^ n)
-- #check (sum_range_succ f n : ∑ x ∈ range (n+1), f x = ∑ x ∈ range n, f x + f n)
-- #check (sum_range_zero f : ∑ k ∈ range 0, f k = 0)

-- Los_limites_son_menores_o_iguales_que_las_cotas_superiores.lean
-- Si x es límite de u e y es cota superior de u, entonces x ≤ y.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla,  2-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, se puede definir que a es el límite de la sucesión u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
-- y que a es una cota superior de u por
--    def cota_superior (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ n, u n ≤ a
--
-- Demostrar que si x es el límite de la sucesión u e y es una cota
-- superior de u, entonces x ≤ y.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usando como lema la propiedad del ejercicio anterior que afirma que
-- para todo x, y ∈ R,
--    (∀ ε > 0, y ≤ x + ε) → y ≤ x
-- la demostración de x ≤ y se reduce a demostrar que
--    ∀ ε > 0, x ≤ y + ε
-- Para demostrarlo, sea ε > 0. Entonces, usando que x es el límite de la
-- sucesión u, existe un k ∈ ℕ tal que
--    ∀ n ≥ k, |u(n) - x| < ε
-- Luego,
--    |u(k) - x| < ε
-- de donde,
--    -ε < u(k) - x
-- y, reordenando,
--    x < u(k) + ε                                                   (1)
-- Por otro lado, pouesto que y es una cota superior de u, se tiene que
--    u(k) < y                                                       (2)
-- De (1) y (2) se obtiene que
--    x < y + ε
-- que es lo que había que demostrar.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable  (u : ℕ → ℝ)
variable (x y : ℝ)

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε

def cota_superior (u : ℕ → ℝ) (a : ℝ) :=
  ∀ n, u n ≤ a

-- Usaremos el lema del ejercicio anterior:
lemma aux :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
by
  contrapose!
  intro h
  use (y-x)/2
  constructor <;> linarith

-- 1º demostración
-- ===============

example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
by
  apply aux
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (le_refl k)
  -- hk : |u k - x| < ε
  replace hk : -ε < u k - x := neg_lt_of_abs_lt hk
  replace hk : x < u k + ε := neg_lt_sub_iff_lt_add'.mp hk
  apply le_of_lt
  -- ⊢ x < y + ε
  exact lt_add_of_lt_add_right hk (hy k)

-- 2º demostración
-- ===============

example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
by
  apply aux
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (le_refl k)
  -- hk : |u k - x| < ε
  apply le_of_lt
  -- ⊢ x < y + ε
  calc x < u k + ε := neg_lt_sub_iff_lt_add'.mp (neg_lt_of_abs_lt hk)
       _ ≤ y + ε   := add_le_add_right (hy k) ε

-- 3º demostración
-- ===============

example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
by
  apply aux
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (by linarith)
  rw [abs_lt] at hk
  -- hk : -ε < u k - x ∧ u k - x < ε
  linarith [hy k]

-- Lemas usados
-- ============

-- variable (n : ℕ)
-- variable (a b c d : ℝ)
-- #check (add_le_add_right : b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)
-- #check (le_of_lt : a < b → a ≤ b)
-- #check (le_refl n : n ≤ n)
-- #check (lt_add_of_lt_add_right : a < b + c → b ≤ d → a < d + c)
-- #check (neg_lt_of_abs_lt : |a| < b → -b < a)
-- #check (neg_lt_sub_iff_lt_add' : -b < a - c ↔ c < a + b)

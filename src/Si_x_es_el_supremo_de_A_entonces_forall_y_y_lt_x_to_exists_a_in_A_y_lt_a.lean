-- Si_x_es_el_supremo_de_A_entonces_forall_y_y_lt_x_to_exists_a_in_A_y_lt_a.lean
-- Si x es el supremo de A, entonces (∀ y, y < x → ∃ a ∈ A, y < a)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-agosto-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4 se puede definir que x es una cota superior de A por
--    def cota_superior (A : set ℝ) (x : ℝ) :=
--      ∀ a ∈ A, a ≤ x
-- y x es el supremo de A por
--    def es_supremo (A : set ℝ) (x : ℝ) :=
--      cota_superior A x ∧ ∀ y, cota_superior A y → x ≤ y
--
-- Demostrar que si x es el supremo de A, entonces
--    ∀ y, y < x → ∃ a ∈ A, y < a
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y < x. Demostraremos que
--    (∃ a ∈ A)[y < a]
-- por reducción al absurdo. Para ello, supongamos que
--    (∀ a ∈ A)[a ≤ y]
-- Entonces, y es una cota superior de A y, como x es supremo de A, se
-- tiene que x ≤ y en contradicción con y < x.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable {A : Set ℝ}
variable {x : ℝ}

def cota_superior (A : Set ℝ) (x : ℝ) :=
  ∀ a ∈ A, a ≤ x

def es_supremo (A : Set ℝ) (x : ℝ) :=
  cota_superior A x ∧ ∀ y, cota_superior A y → x ≤ y

-- 1ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  have h1 : cota_superior A y := h
  have h2 : x ≤ y := hx.2 y h1
  have h3 : ¬x ≤ y := not_le.mpr hy
  exact h3 h2

-- 2ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  have h1 : x ≤ y := hx.2 y h
  replace h1 : ¬(y < x) := not_lt_of_le h1
  exact h1 hy

-- 3ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  apply absurd hy
  -- ⊢ ¬y < x
  apply not_lt_of_le
  -- ⊢ x ≤ y
  apply hx.2 y
  -- ⊢ cota_superior A y
  exact h

-- 4ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  by_contra h
  -- h : ¬∃ a ∈ A, y < a
  -- ⊢ False
  push_neg at h
  -- h : ∀ a ∈ A, a ≤ y
  exact absurd hy (not_lt_of_le (hx.2 y h))

-- 5ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  contrapose hy
  -- hy : ¬∃ a ∈ A, y < a
  -- ⊢ ¬y < x
  push_neg at hy
  -- hy : ∀ a ∈ A, a ≤ y
  push_neg
  -- ⊢ x ≤ y
  unfold es_supremo at hx
  -- hx : cota_superior A x ∧ ∀ (y : ℝ), cota_superior A y → x ≤ y
  rcases hx with ⟨_, h2⟩
  -- h2 : ∀ (y : ℝ), cota_superior A y → x ≤ y
  apply h2 y
  -- h2 : ∀ (y : ℝ), cota_superior A y → x ≤ y
  unfold cota_superior
  -- ⊢ ∀ a ∈ A, a ≤ y
  exact hy

-- 6ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  contrapose hy
  -- hy : ¬∃ a ∈ A, y < a
  -- ⊢ ¬y < x
  push_neg at hy
  -- hy : ∀ a ∈ A, a ≤ y
  push_neg
  -- ⊢ x ≤ y
  rcases hx with ⟨-, h2⟩
  -- h2 : ∀ (y : ℝ), cota_superior A y → x ≤ y
  exact h2 y hy

-- 7ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intros y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  contrapose hy
  -- hy : ¬∃ a ∈ A, y < a
  -- ⊢ ¬y < x
  push_neg at hy
  -- hy : ∀ a ∈ A, a ≤ y
  push_neg
  -- ⊢ x ≤ y
  exact hx.right y hy

-- 8ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intro y
  -- y : ℝ
  -- ⊢ y < x → ∃ a ∈ A, y < a
  contrapose!
  -- ⊢ (∀ a ∈ A, a ≤ y) → x ≤ y
  exact hx.right y

-- 9ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
by
  intro y hy
  -- y : ℝ
  -- hy : y < x
  -- ⊢ ∃ a ∈ A, y < a
  exact (lt_isLUB_iff hx).mp hy

-- 10ª demostración
-- ===============

example
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
fun _ hy ↦ (lt_isLUB_iff hx).mp hy

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- variable (p q : Prop)
-- #check (absurd : p → ¬p → q)
-- #check (lt_isLUB_iff : IsLUB A a → (b < a ↔ ∃ c ∈ A, b < c))
-- #check (not_le : ¬a ≤ b ↔ b < a)
-- #check (not_lt_of_le : a ≤ b → ¬b < a)

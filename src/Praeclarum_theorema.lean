-- Praeclarum_theorema.lean
-- Praeclarum theorema
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-enero-2025
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar el [praeclarum theorema](https://tinyurl.com/25yt3ef9) de
-- Leibniz:
--    (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s))
-- ---------------------------------------------------------------------

import Mathlib.Tactic

variable (p q r s : Prop)

-- 1ª demostración
-- ===============

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
by
  intro ⟨hpq, hrs⟩ ⟨hp, hr⟩
  -- hpq : p → q
  -- hrs : r → s
  -- hp : p
  -- hr : r
  constructor
  . -- q
    exact hpq hp
  . -- s
    exact hrs hr

-- 2ª demostración
-- ===============

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
by
  intro ⟨hpq, hrs⟩ ⟨hp, hr⟩
  -- hpq : p → q
  -- hrs : r → s
  -- hp : p
  -- hr : r
  exact ⟨hpq hp, hrs hr⟩

-- 3ª demostración
-- ===============

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
fun ⟨hpq, hrs⟩ ⟨hp, hr⟩ ↦ ⟨hpq hp, hrs hr⟩

-- 4ª demostración
-- ===============

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
fun ⟨hpq, hrs⟩ hpr ↦ And.imp hpq hrs hpr

-- 5ª demostración
-- ===============

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
by aesop

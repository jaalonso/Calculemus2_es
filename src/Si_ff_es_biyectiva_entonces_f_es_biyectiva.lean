-- Si_ff_es_biyectiva_entonces_f_es_biyectiva.lean
-- Si f ∘ f es biyectiva, entonces f es biyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f ∘ f es biyectiva, entonces f es biyectiva.
-- ---------------------------------------------------------------------

import Mathlib.Tactic
open Function

variable {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

-- 1ª demostración
-- ===============

example
  (f : X → X)
  (h : Bijective (f ∘ f))
  : Bijective f :=
by
  constructor
  . -- ⊢ Injective f
    have h1 : Injective (f ∘ f) := Bijective.injective h
    exact Injective.of_comp h1
  . -- ⊢ Surjective f
    have h2 : Surjective (f ∘ f) := Bijective.surjective h
    exact Surjective.of_comp h2

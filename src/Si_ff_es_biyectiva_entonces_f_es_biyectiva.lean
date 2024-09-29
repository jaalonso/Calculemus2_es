-- Si_ff_es_biyectiva_entonces_f_es_biyectiva.lean
-- Si f ∘ f es biyectiva, entonces f es biyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f ∘ f es biyectiva, entonces f es biyectiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Es consecuencia de los siguientes lemas (demostrados en ejercicios
-- anteriores):
-- + Lema 1: Si g ∘ f es inyectiva. entonces f es inyectiva.
-- + Lema 2: Si g ∘ f es suprayectiva. entonces g es suprayectiva.
-- En efecto, supongamos que
--    f ∘ f es biyectiva
-- entonces se tiene que
--    f ∘ f es inyectiva                                             (1)
--    f ∘ f es suprayectiva                                          (2)
-- De (1) y el Lema 1, se tiene que
--    f es inyectiva                                                 (3)
-- De (2) y el Lema 2, se tiene que
--    f es suprayectiva                                              (4)
-- De (3) y (4) se tiene que
--    f es biyectiva

-- Demostraciones con Lean4
-- ========================

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
  have h1 : Injective (f ∘ f) := Bijective.injective h
  have h2 : Surjective (f ∘ f) := Bijective.surjective h
  have h3 : Injective f := Injective.of_comp h1
  have h4 : Surjective f := Surjective.of_comp h2
  show Bijective f
  exact ⟨h3, h4⟩

-- 2ª demostración
-- ===============

example
  (f : X → X)
  (h : Bijective (f ∘ f))
  : Bijective f :=
⟨Injective.of_comp (Bijective.injective h),
 Surjective.of_comp (Bijective.surjective h)⟩

-- 3ª demostración
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

-- Lemas usados
-- ============

-- #check (Injective.of_comp : Injective (g ∘ f) → Injective f)
-- #check (Surjective.of_comp : Surjective (g ∘ f) → Surjective g)

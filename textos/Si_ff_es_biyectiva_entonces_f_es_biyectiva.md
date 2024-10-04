---
title: Si f ∘ f es biyectiva, entonces f es biyectiva
date: 2024-09-30 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

Demostrar que si \\(f ∘ f\\) es biyectiva, entonces \\(f\\) es biyectiva.

Para ello, completar la siguiente teoría de Lean4:

~~~lean
import Mathlib.Tactic
open Function

variable {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

example
  (f : X → X)
  (h : Bijective (f ∘ f))
  : Bijective f :=
by sorry
~~~
<!-- TEASER_END -->

# 1. Demostración en lenguaje natural

Es consecuencia de los siguientes lemas (demostrados en ejercicios anteriores):

+ Lema 1: Si \\(g ∘ f\\) es inyectiva. entonces \\(f\\) es inyectiva.
+ Lema 2: Si \\(g ∘ f\\) es suprayectiva. entonces \\(g\\) es suprayectiva.

En efecto, supongamos que
\\[ f ∘ f \\text{ es biyectiva} \\]
entonces se tiene que
\\begin{align}
   &f ∘ f \\text{ es inyectiva}    \\tag{1} \\newline
   &f ∘ f \\text{ es suprayectiva} \\tag{2}
\\end{align}
De (1) y el Lema 1, se tiene que
\\[ f \\text{ es inyectiva} \\tag{3} \\]
De (2) y el Lema 2, se tiene que
\\[ f \\text{ es suprayectiva} \\tag{4} \\]
De (3) y (4) se tiene que
\\[ f \\text{ es biyectiva} \\]

# 2. Demostraciones con Lean4

~~~lean
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
~~~

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Si_ff_es_biyectiva_entonces_f_es_biyectiva.lean).

# 3. Demostraciones con Isabelle/HOL

~~~isabelle
theory Si_ff_es_biyectiva_entonces_f_es_biyectiva
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "bij (f ∘ f)"
  shows   "bij f"
proof (rule bijI)
  show "inj f"
  proof -
    have h1 : "inj (f ∘ f)"
      using assms by (simp only: bij_is_inj)
    then show "inj f"
      by (simp only: inj_on_imageI2)
  qed
next
  show "surj f"
  proof -
    have h2 : "surj (f ∘ f)"
      using assms by (simp only: bij_is_surj)
    then show "surj f"
      by auto
  qed
qed

(* 2ª demostración *)
lemma
  assumes "bij (f ∘ f)"
  shows   "bij f"
proof (rule bijI)
  show "inj f"
    using assms bij_is_inj inj_on_imageI2
    by blast
next
  show "surj f"
    using assms bij_is_surj
    by fastforce
qed

(* 3 demostración *)
lemma
  assumes "bij (f ∘ f)"
  shows   "bij f"
by (metis assms
          bij_betw_comp_iff
          bij_betw_def
          bij_betw_imp_surj
          inj_on_imageI2)

end
~~~

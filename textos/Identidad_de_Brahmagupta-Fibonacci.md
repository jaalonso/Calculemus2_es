---
title: Identidad de Brahmagupta-Fibonacci
date: 2024-09-25 06:00:00 UTC+02:00
category: Números reales
has_math: true
---

Demostrar la [identidad de Brahmagupta-Fibonacci](https://is.gd/9PJ56H)
\\[ (a^2 + b^2)(c^2 + d^2) = (ac - bd)^2 + (ad + bc)^2 \\]

Para ello, completar la siguiente teoría de Lean4:

~~~lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c d : ℝ)

example : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
sorry
~~~
<!-- TEASER_END -->

# 1. Demostración en lenguaje natural

Se demuestra por la siguiente cadena de igualdades
\\begin{align}
   (a^2 + b^2)(c^2 + d^2) &= a^2(c^2 + d^2) + b^2(c^2 + d^2)       \\newline
                          &= (a^2c^2 + a^2d^2) + (b^2c^2 + b^2d^2) \\newline
                          &= ((ac)^2 + (bd)^2) + ((ad)^2 + (bc)^2) \\newline
                          &= ((ac)^2 - 2acbd + (bd)^2) + ((ad)^2 + 2adbc + (bc)^2) \\newline
                          &= (ac - bd)^2 + (ad + bc)^2
\\end{align}

# 2. Demostraciones con Lean4

~~~lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c d : ℝ)

-- 1ª demostración
-- ===============

example : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
calc (a^2 + b^2) * (c^2 + d^2)
     = a^2 * (c^2 + d^2) + b^2 * (c^2 + d^2)
         := right_distrib (a^2) (b^2) (c^2 + d^2)
   _ = (a^2*c^2 + a^2*d^2) + b^2 * (c^2 + d^2)
         := congr_arg₂ (. + .) (left_distrib (a^2) (c^2) (d^2)) rfl
   _ = (a^2*c^2 + a^2*d^2) + (b^2*c^2 + b^2*d^2)
         := congr_arg₂ (. + .) rfl (left_distrib (b^2) (c^2) (d^2))
   _ = ((a*c)^2 + (b*d)^2) + ((a*d)^2 + (b*c)^2)
         := by ring
   _ = ((a*c)^2 - 2*a*c*b*d + (b*d)^2) + ((a*d)^2 + 2*a*d*b*c + (b*c)^2)
         := by ring
   _ = (a*c - b*d)^2 + (a*d + b*c)^2
         := by ring

-- 2ª demostración
-- ===============

example : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
by ring

-- Lemas usados
-- ============

-- variable (f : ℝ → ℝ → ℝ)
-- variable (x x' y y' : ℝ)
-- #check (congr_arg₂ f : x = x' → y = y' → f x y = f x' y')
-- #check (left_distrib a b c : a * (b + c) = a * b + a * c)
-- #check (right_distrib a b c: (a + b) * c = a * c + b * c)
~~~

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Identidad_de_Brahmagupta-Fibonacci.lean).

# 3. Demostraciones con Isabelle/HOL

~~~isabelle
theory "Identidad_de_Brahmagupta-Fibonacci"
imports Main HOL.Real
begin

(* 1ª demostración *)
lemma
  fixes a b c d :: real
  shows "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2"
proof -
  have "(a^2 + b^2) * (c^2 + d^2) = a^2 * (c^2 + d^2) + b^2 * (c^2 + d^2)"
    by (simp only: distrib_right)
  also have "… = (a^2*c^2 + a^2*d^2) + b^2 * (c^2 + d^2)"
    by (simp only: distrib_left)
  also have "… = (a^2*c^2 + a^2*d^2) + (b^2*c^2 + b^2*d^2)"
    by (simp only: distrib_left)
  also have "… = ((a*c)^2 + (b*d)^2) + ((a*d)^2 + (b*c)^2)"
    by algebra
  also have "… = ((a*c)^2 - 2*a*c*b*d + (b*d)^2) +
                  ((a*d)^2 + 2*a*d*b*c + (b*c)^2)"
    by algebra
  also have "… = (a*c - b*d)^2 + (a*d + b*c)^2"
    by algebra
  finally show "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2" .
qed

(* 2ª demostración *)
lemma
  fixes a b c d :: real
  shows "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2"
by algebra

end
~~~

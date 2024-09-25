(* Identidad_de_Brahmagupta-Fibonacci.thy
-- Identidad de Brahmagupta-Fibonacci
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar la identidad de Brahmagupta-Fibonacci https://is.gd/9PJ56H
--    (a² + b²) * (c² + d²) = (ac - bd)² + (ad + bc)²
-- ------------------------------------------------------------------ *)

theory "Identidad_de_Brahmagupta-Fibonacci"
imports Main HOL.Real
begin

(* 1\<ordfeminine> demostración *)
lemma
  fixes a b c d :: real
  shows "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2"
proof -
  have "(a^2 + b^2) * (c^2 + d^2) = a^2 * (c^2 + d^2) + b^2 * (c^2 + d^2)"
    by (simp only: distrib_right)
  also have "\<dots> = (a^2*c^2 + a^2*d^2) + b^2 * (c^2 + d^2)"
    by (simp only: distrib_left)
  also have "\<dots> = (a^2*c^2 + a^2*d^2) + (b^2*c^2 + b^2*d^2)"
    by (simp only: distrib_left)
  also have "\<dots> = ((a*c)^2 + (b*d)^2) + ((a*d)^2 + (b*c)^2)"
    by algebra
  also have "\<dots> = ((a*c)^2 - 2*a*c*b*d + (b*d)^2) + 
                  ((a*d)^2 + 2*a*d*b*c + (b*c)^2)"
    by algebra
  also have "\<dots> = (a*c - b*d)^2 + (a*d + b*c)^2"
    by algebra
  finally show "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2" .
qed

(* 2\<ordfeminine> demostración *)
lemma
  fixes a b c d :: real
  shows "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2"
by algebra

end

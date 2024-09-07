(* Suma_de_progresion_aritmetica.lean
-- Pruebas de a+(a+d)+(a+2d)+\<sqdot>\<sqdot>\<sqdot>+(a+nd)=(n+1)(2a+nd)/2
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que la suma de los términos de la progresión aritmética
--    a + (a + d) + (a + 2 \<times> d) + \<sqdot>\<sqdot>\<sqdot> + (a + n \<times> d)
-- es (n + 1) \<times> (2 \<times> a + n \<times> d) / 2.
-- ------------------------------------------------------------------ *)

theory Suma_de_progresion_aritmetica
imports Main HOL.Real
begin

fun sumaPA :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "sumaPA a d 0 = a"
| "sumaPA a d (Suc n) = sumaPA a d n + (a + (n + 1) * d)"

(* 1\<ordfeminine> demostración *)
lemma
  "2 * sumaPA a d n = (n + 1) * (2 * a + n * d)"
proof (induct n)
  show "2 * sumaPA a d 0 =
        (real 0 + 1) * (2 * a + real 0 * d)"
    by simp
next
  fix n
  assume HI : "2 * sumaPA a d n =
               (n + 1) * (2 * a + n * d)"
  have "2 * sumaPA a d (Suc n) =
        2 * (sumaPA a d n + (a + (n + 1) * d))"
    by simp
  also have "\<dots> = 2 * sumaPA a d n + 2 * (a + (n + 1) * d)"
    by simp
  also have "\<dots> = (n + 1) * (2 * a + n * d) + 2 * (a + (n + 1) * d)"
    using HI by simp
  also have "\<dots> = (real (Suc n) + 1) * (2 * a + (Suc n) * d)"
    by (simp add: algebra_simps)
  finally show "2 * sumaPA a d (Suc n) =
                (real (Suc n) + 1) * (2 * a + (Suc n) * d)"
    by this
qed

(* 2\<ordfeminine> demostración *)
lemma
  "2 * sumaPA a d n = (n + 1) * (2*a + n*d)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: algebra_simps)
qed

(* 3\<ordfeminine> demostración *)
lemma
  "2 * sumaPA a d n = (n + 1) * (2*a + n*d)"
by (induct n) (simp_all add: algebra_simps)

end

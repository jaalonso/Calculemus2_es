(* Suma_de_progresion_geometrica.thy
-- Pruebas de a+aq+aq²+···+aqⁿ = a(1-qⁿ⁺¹)/(1-q)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla,  8-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que la suma de los términos de la progresión geométrica
--    a + aq + aq² + \<sqdot>\<sqdot>\<sqdot> + aq\<^sup>nⁿ
-- es
--      a(1 - q\<^sup>n\<^sup>+\<^sup>1)
--    -------------
--        1 - q
-- ------------------------------------------------------------------ *)

theory Suma_de_progresion_geometrica
imports Main HOL.Real
begin

fun sumaPG :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "sumaPG a q 0 = a"
| "sumaPG a q (Suc n) = sumaPG a q n + (a * q^(n + 1))"

(* 1\<ordfeminine> demostración *)
lemma
  "(1 - q) * sumaPG a q n = a * (1 - q^(n + 1))"
proof (induct n)
  show "(1 - q) * sumaPG a q 0 = a * (1 - q ^ (0 + 1))"
    by simp
next
  fix n
  assume HI : "(1 - q) * sumaPG a q n = a * (1 - q ^ (n + 1))"
  have "(1 - q) * sumaPG a q (Suc n) =
        (1 - q) * (sumaPG a q n + (a * q^(n + 1)))"
    by simp
  also have "\<dots> = (1 - q) * sumaPG a q n + (1 - q) * a * q^(n + 1)"
    by (simp add: algebra_simps)
  also have "\<dots> = a * (1 - q ^ (n + 1)) + (1 - q) * a * q^(n + 1)"
    using HI by simp
  also have "\<dots> = a * (1 - q ^ (n + 1) + (1 - q) * q^(n + 1))"
    by (simp add: algebra_simps)
  also have "\<dots> = a * (1 - q ^ (n + 1) +  q^(n + 1) - q^(n + 2))"
    by (simp add: algebra_simps)
  also have "\<dots> = a * (1 - q^(n + 2))"
    by simp
  also have "\<dots> = a * (1 - q ^ (Suc n + 1))"
    by simp
  finally show "(1 - q) * sumaPG a q (Suc n) = a * (1 - q ^ (Suc n + 1))"
    by this
qed

(* 2\<ordfeminine> demostración *)
lemma
  "(1 - q) * sumaPG a q n = a * (1 - q^(n + 1))"
proof (induct n)
  show "(1 - q) * sumaPG a q 0 = a * (1 - q ^ (0 + 1))"
    by simp
next
  fix n
  assume HI : "(1 - q) * sumaPG a q n = a * (1 - q ^ (n + 1))"
  have "(1 - q) * sumaPG a q (Suc n) =
        (1 - q) * sumaPG a q n + (1 - q) * a * q^(n + 1)"
    by (simp add: algebra_simps)
  also have "\<dots> = a * (1 - q ^ (n + 1)) + (1 - q) * a * q^(n + 1)"
    using HI by simp
  also have "\<dots> = a * (1 - q ^ (n + 1) +  q^(n + 1) - q^(n + 2))"
    by (simp add: algebra_simps)
  finally show "(1 - q) * sumaPG a q (Suc n) = a * (1 - q ^ (Suc n + 1))"
    by simp
qed

(* 3\<ordfeminine> demostración *)
lemma
  "(1 - q) * sumaPG a q n = a * (1 - q^(n + 1))"
  using power_add
  by (induct n) (auto simp: algebra_simps)

end

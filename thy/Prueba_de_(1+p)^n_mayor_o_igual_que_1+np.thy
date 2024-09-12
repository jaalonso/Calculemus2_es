(* Prueba_de_(1+p)^n_mayor_o_igual_que_1+np.thy
-- Pruebas de "Si p > -1, entonces (1+p)ⁿ \<ge> 1+np"
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sean p \<in> \<real> y n \<in> \<nat> tales que p > -1. Demostrar que
--    (1 + p)^n \<ge> 1 + n*p
-- ------------------------------------------------------------------ *)

theory "Prueba_de_(1+p)^n_mayor_o_igual_que_1+np"
imports Main HOL.Real
begin

lemma
  fixes p :: real
  assumes "p > -1"
  shows "(1 + p)^n \<ge> 1 + n*p"
proof (induct n)
  show "(1 + p) ^ 0 \<ge> 1 + real 0 * p"
    by simp
next
  fix n
  assume HI : "(1 + p)^n \<ge> 1 +  n * p"
  have "1 + Suc n * p = 1 + (n + 1) * p"
    by simp
  also have "\<dots> = 1 + n*p + p"
    by (simp add: distrib_right)
  also have "\<dots> \<le> (1 + n*p + p) + n*(p*p)"
    by simp
  also have "\<dots> = (1 + n * p) * (1 + p)"
    by algebra
  also have "\<dots> \<le> (1 + p)^n * (1 + p)"
    using HI assms by simp
  also have "\<dots> = (1 + p)^(Suc n)"
    by simp
  finally show "1 + Suc n * p \<le> (1 + p)^(Suc n)" .
qed

end

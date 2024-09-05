(* Suma_de_los_primeros_n_numeros_naturales.thy
-- Prueba de "0 + 1 + 2 + 3 + \<sqdot>\<sqdot>\<sqdot> + n = n \<times> (n + 1)/2"
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla,  5-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que la suma de los números naturales
--    0 + 1 + 2 + 3 + \<sqdot>\<sqdot>\<sqdot> + n
-- es n \<times> (n + 1)/2
-- ------------------------------------------------------------------ *)

theory Suma_de_los_primeros_n_numeros_naturales
imports Main
begin

fun suma :: "nat \<Rightarrow> nat" where
  "suma 0       = 0"
| "suma (Suc n) = suma n + Suc n"

(* 1\<ordfeminine> demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  have "2 * suma 0 = 2 * 0"
    by (simp only: suma.simps(1))
  also have "\<dots> = 0"
    by (rule mult_0_right)
  also have "\<dots> = 0 * (0 + 1)"
    by (rule mult_0 [symmetric])
  finally show "2 * suma 0 = 0 * (0 + 1)"
    by this
next
  fix n
  assume HI : "2 * suma n = n * (n + 1)"
  have "2 * suma (Suc n) = 2 * (suma n + Suc n)"
    by (simp only: suma.simps(2))
  also have "\<dots> = 2 * suma n + 2 * Suc n"
    by (rule add_mult_distrib2)
  also have "\<dots> = n * (n + 1) + 2 * Suc n"
    by (simp only: HI)
  also have "\<dots> = n * (n + Suc 0) + 2 * Suc n"
    by (simp only: One_nat_def)
  also have "\<dots> = n * Suc (n + 0) + 2 * Suc n"
    by (simp only: add_Suc_right)
  also have "\<dots> = n * Suc n + 2 * Suc n"
    by (simp only: add_0_right)
  also have "\<dots> = (n + 2) * Suc n"
    by (simp only: add_mult_distrib)
  also have "\<dots> = Suc (Suc n) * Suc n"
    by (simp only: add_2_eq_Suc')
  also have "\<dots> = (Suc n + 1) * Suc n"
    by (simp only: Suc_eq_plus1)
  also have "\<dots> = Suc n * (Suc n + 1)"
    by (simp only: mult.commute)
  finally show "2 * suma (Suc n) = Suc n * (Suc n + 1)"
    by this
qed

(* 2\<ordfeminine> demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  have "2 * suma 0 = 2 * 0" by simp
  also have "\<dots> = 0" by simp
  also have "\<dots> = 0 * (0 + 1)" by simp
  finally show "2 * suma 0 = 0 * (0 + 1)" .
next
  fix n
  assume HI : "2 * suma n = n * (n + 1)"
  have "2 * suma (Suc n) = 2 * (suma n + Suc n)" by simp
  also have "\<dots> = 2 * suma n + 2 * Suc n" by simp
  also have "\<dots> = n * (n + 1) + 2 * Suc n" using HI by simp
  also have "\<dots> = n * (n + Suc 0) + 2 * Suc n" by simp
  also have "\<dots> = n * Suc (n + 0) + 2 * Suc n" by simp
  also have "\<dots> = n * Suc n + 2 * Suc n" by simp
  also have "\<dots> = (n + 2) * Suc n" by simp
  also have "\<dots> = Suc (Suc n) * Suc n" by simp
  also have "\<dots> = (Suc n + 1) * Suc n" by simp
  also have "\<dots> = Suc n * (Suc n + 1)" by simp
  finally show "2 * suma (Suc n) = Suc n * (Suc n + 1)" .
qed

(* 3\<ordfeminine> demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  have "2 * suma 0 = 2 * 0" by simp
  also have "\<dots> = 0" by simp
  also have "\<dots> = 0 * (0 + 1)" by simp
  finally show "2 * suma 0 = 0 * (0 + 1)" .
next
  fix n
  assume HI : "2 * suma n = n * (n + 1)"
  have "2 * suma (Suc n) = 2 * (suma n + Suc n)" by simp
  also have "\<dots> = n * (n + 1) + 2 * Suc n" using HI by simp
  also have "\<dots> = (n + 2) * Suc n" by simp
  also have "\<dots> = Suc n * (Suc n + 1)" by simp
  finally show "2 * suma (Suc n) = Suc n * (Suc n + 1)" .
qed

(* 4\<ordfeminine> demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  show "2 * suma 0 = 0 * (0 + 1)" by simp
next
  fix n
  assume "2 * suma n = n * (n + 1)"
  then show "2 * suma (Suc n) = Suc n * (Suc n + 1)" by simp
qed

(* 5\<ordfeminine> demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* 6\<ordfeminine> demostración *)
lemma
  "2 * suma n = n * (n + 1)"
by (induct n) simp_all

end

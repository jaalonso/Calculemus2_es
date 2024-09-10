(* Suma_de_los_primeros_cubos.thy
-- Pruebas de 0³+1³+2³+3³+···+n³ = (n(n+1)/2)²
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que la suma de los primeros cubos
--    0³ + 1³ + 2³ + 3³ + \<sqdot>\<sqdot>\<sqdot> + n³
-- es (n(n+1)/2)²
-- ------------------------------------------------------------------ *)

theory Suma_de_los_primeros_cubos
imports Main
begin

fun sumaCubos :: "nat \<Rightarrow> nat" where
  "sumaCubos 0       = 0"
| "sumaCubos (Suc n) = sumaCubos n + (Suc n)^3"

(* 1\<ordfeminine> demostración *)
lemma
  "4 * sumaCubos n = (n*(n+1))^2"
proof (induct n)
  show "4 * sumaCubos 0 = (0 * (0 + 1))^2"
    by simp
next
  fix n
  assume HI : "4 * sumaCubos n = (n * (n + 1))^2"
  have "4 * sumaCubos (Suc n) = 4 * (sumaCubos n + (n+1)^3)"
    by simp
  also have "\<dots> = 4 * sumaCubos n + 4*(n+1)^3"
    by simp
  also have "\<dots> = (n*(n+1))^2 + 4*(n+1)^3"
    using HI by simp
  also have "\<dots> = (n+1)^2*(n^2+4*n+4)"
    by algebra
  also have "\<dots> = (n+1)^2*(n+2)^2"
    by algebra
  also have "\<dots> = ((n+1)*((n+1)+1))^2"
    by algebra
  also have "\<dots> = (Suc n * (Suc n + 1))^2"
    by (simp only: Suc_eq_plus1)
  finally show "4 * sumaCubos (Suc n) = (Suc n * (Suc n + 1))^2"
    by this
qed

(* 2\<ordfeminine> demostración *)
lemma
  "4 * sumaCubos n = (n*(n+1))^2"
proof (induct n)
  show "4 * sumaCubos 0 = (0 * (0 + 1))^2"
    by simp
next
  fix n
  assume HI : "4 * sumaCubos n = (n * (n + 1))^2"
  have "4 * sumaCubos (Suc n) = 4 * sumaCubos n + 4*(n+1)^3"
    by simp
  also have "\<dots> = (n*(n+1))^2 + 4*(n+1)^3"
    using HI by simp
  also have "\<dots> = ((n+1)*((n+1)+1))^2"
    by algebra
  also have "\<dots> = (Suc n * (Suc n + 1))^2"
    by (simp only: Suc_eq_plus1)
  finally show "4 * sumaCubos (Suc n) = (Suc n * (Suc n + 1))^2" .
qed

end

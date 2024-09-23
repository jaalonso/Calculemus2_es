(* Suma_de_potencias_de_dos.lean
-- Pruebas de \<Sum>k<n. 2^k = 2^n-1
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    1 + 2 + 2² + 2³ + ... + 2\<^sup>n⁾= 2\<^sup>n\<^sup>+\<^sup>1 - 1
-- ------------------------------------------------------------------ *)

theory Suma_de_potencias_de_dos
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  show "(\<Sum>k\<le>0. (2::nat)^k) = 2^(0+1) - 1"
    by simp
next
  fix n
  assume HI : "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
  have "(\<Sum>k\<le>Suc n. (2::nat)^k) =
        (\<Sum>k\<le>n. (2::nat)^k) + 2^Suc n"
    by simp
  also have "\<dots> = (2^(n+1) - 1) + 2^Suc n"
    using HI by simp
  also have "\<dots> = 2^(Suc n + 1) - 1"
    by simp
  finally show "(\<Sum>k\<le>Suc n. (2::nat)^k) = 2^(Suc n + 1) - 1" .
qed

(* 2\<ordfeminine> demostración *)
lemma "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  show "(\<Sum>k\<le>0. (2::nat)^k) = 2^(0+1) - 1"
    by simp
next
  fix n
  assume HI : "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
  have "(\<Sum>k\<le>Suc n. (2::nat)^k) =
        (2^(n+1) - 1) + 2^Suc n"
    using HI by simp
  then show "(\<Sum>k\<le>Suc n. (2::nat)^k) = 2^(Suc n + 1) - 1"
    by simp
qed

(* 3\<ordfeminine> demostración *)
lemma "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* 4\<ordfeminine> demostración *)
lemma "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
by (induct n) simp_all

end

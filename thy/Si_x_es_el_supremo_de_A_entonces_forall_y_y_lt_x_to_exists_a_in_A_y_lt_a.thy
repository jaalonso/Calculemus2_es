(* Si_x_es_el_supremo_de_A_entonces_forall_y_y_lt_x_to_exists_a_in_A_y_lt_a.lean
-- Si x es el supremo de A, entonces (\<forall> y, y < x \<rightarrow> \<exists> a \<in> A, y < a)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-agosto-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL se puede definir que x es una cota superior de A por
--    definition cota_superior :: "(real set) \<Rightarrow> real \<Rightarrow> bool" where
--      "cota_superior A x \<longleftrightarrow> (\<forall>a\<in>A. a \<le> x)"
-- y x es el supremo de A por
--    definition es_supremo :: "(real set) \<Rightarrow> real \<Rightarrow> bool" where
--      "es_supremo A x \<longleftrightarrow> (cota_superior A x \<and>
--                           (\<forall> y. cota_superior A y \<longrightarrow> x \<le> y))"
--
-- Demostrar que si x es el supremo de A, entonces
--    "\<forall>y<x. \<exists>a\<in>A. y < a"
-- ------------------------------------------------------------------ *)

theory "Si_x_es_el_supremo_de_A_entonces_forall_y_y_lt_x_to_exists_a_in_A_y_lt_a"
  imports Main HOL.Real
begin

definition cota_superior :: "(real set) \<Rightarrow> real \<Rightarrow> bool" where
  "cota_superior A x \<longleftrightarrow> (\<forall>a\<in>A. a \<le> x)"

definition es_supremo :: "(real set) \<Rightarrow> real \<Rightarrow> bool" where
  "es_supremo A x \<longleftrightarrow> (cota_superior A x \<and>
                       (\<forall> y. cota_superior A y \<longrightarrow> x \<le> y))"

(* 1\<ordfeminine> demostración *)
lemma
  assumes "es_supremo A x"
  shows   "\<forall>y<x. \<exists>a\<in>A. y < a"
proof (intro allI impI)
  fix y
  assume "y < x"
  show "\<exists>a\<in>A. y < a"
  proof (rule ccontr)
    assume "\<not> (\<exists>a\<in>A. y < a)"
    then have "\<forall>a\<in>A. a \<le> y"
      by auto
    then have "cota_superior A y"
      using cota_superior_def by simp
    then have "x \<le> y"
      using assms es_supremo_def by simp
    then have "x < x"
      using \<open>y < x\<close> by simp
    then show False by simp
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma
  assumes "es_supremo A x"
  shows   "\<forall>y<x. \<exists>a\<in>A. y < a"
proof (intro allI impI)
  fix y
  assume "y < x"
  show "\<exists>a\<in>A. y < a"
  proof (rule ccontr)
    assume "\<not> (\<exists>a\<in>A. y < a)"
    then have "cota_superior A y"
      using cota_superior_def by auto
    then show "False"
      using assms es_supremo_def \<open>y < x\<close> by auto
  qed
qed

end

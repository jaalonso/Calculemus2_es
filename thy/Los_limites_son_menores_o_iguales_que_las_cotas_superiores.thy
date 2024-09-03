(* Los_limites_son_menores_o_iguales_que_las_cotas_superiores.thy
-- Si x es límite de u e y es cota superior de u, entonces x \<le> y.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla,  2-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, se puede definir que a es el límite de la sucesión u
-- por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
--      "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
-- y que a es una cota superior de  u por
--    definition cota_superior :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
--      "cota_superior u c \<longleftrightarrow> (\<forall>n. u n \<le> c)"
--
-- Demostrar que si x es el límite de la sucesión u e y es una cota
-- superior de u, entonces x \<le> y.
-- ------------------------------------------------------------------ *)

theory Los_limites_son_menores_o_iguales_que_las_cotas_superiores
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

definition cota_superior :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "cota_superior u c \<longleftrightarrow> (\<forall>n. u n \<le> c)"

(* 1\<ordfeminine> demostración *)
lemma
  fixes x y :: real
  assumes "limite u x"
          "cota_superior u y"
  shows   "x \<le> y"
proof (rule field_le_epsilon)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - x\<bar> < \<epsilon>"
    using assms(1) limite_def by auto
  then have "\<bar>u k - x\<bar> < \<epsilon>"
    by simp
  then have "-\<epsilon> < u k - x"
    by simp
  then have "x < u k + \<epsilon>"
    by simp
  moreover have "u k \<le> y"
    using assms(2) cota_superior_def by simp
  ultimately show "x \<le> y + \<epsilon>"
    by simp
qed

(* 2\<ordfeminine> demostración *)
lemma
  fixes x y :: real
  assumes "limite u x"
          "cota_superior u y"
  shows   "x \<le> y"
proof (rule field_le_epsilon)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - x\<bar> < \<epsilon>"
    using assms(1) limite_def by auto
  then have "x < u k + \<epsilon>"
    by auto
  moreover have "u k \<le> y"
    using assms(2) cota_superior_def by simp
  ultimately show "x \<le> y + \<epsilon>"
    by simp
qed

(* 3\<ordfeminine> demostración *)
lemma
  fixes x y :: real
  assumes "limite u x"
          "cota_superior u y"
  shows   "x \<le> y"
proof (rule field_le_epsilon)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - x\<bar> < \<epsilon>"
    using assms(1) limite_def by auto
  then show "x \<le> y + \<epsilon>"
    using assms(2) cota_superior_def 
    by (smt (verit) order_refl)
qed

end

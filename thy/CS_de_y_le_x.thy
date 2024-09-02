(* CS_de_y_le_x.thy
-- Si (∀ ε > 0, y ≤ x + ε), entonces y ≤ x
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    (\<forall>\<epsilon>>0. y \<le> x + \<epsilon>) \<longrightarrow> y \<le> x
-- ------------------------------------------------------------------- *)

theory CS_de_y_le_x
imports Main HOL.Real
begin

(* 1\<ordfeminine> demostración *)
lemma
  fixes x y :: real
  shows "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>) \<longrightarrow> y \<le> x"
proof (rule impI)
  assume h1 : "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>)"
  show "y \<le> x"
  proof (rule ccontr)
    assume "\<not> (y \<le> x)"
    then have "x < y"
      by simp
    then have "(y - x) / 2 > 0"
      by simp
    then have "y \<le> x + (y - x) / 2"
      using h1 by blast
    then have "2 * y \<le> 2 * x + (y - x)"
      by argo
    then have "y \<le> x"
      by simp
    then show False
      using \<open>\<not> (y \<le> x)\<close> by simp
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma
  fixes x y :: real
  shows "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>) \<longrightarrow> y \<le> x"
proof (rule impI)
  assume h1 : "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>)"
  show "y \<le> x"
  proof (rule ccontr)
    assume "\<not> (y \<le> x)"
    then have "x < y"
      by simp
    then obtain z where hz : "x < z \<and> z < y"
      using Rats_dense_in_real by blast
    then have "0 < z -x"
      by simp
    then have "y \<le> x + (z - x)"
      using h1 by blast
    then have "y \<le> z"
      by simp
    then show False
      using hz by simp
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma
  fixes x y :: real
  shows "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>) \<longrightarrow> y \<le> x"
proof (rule impI)
  assume h1 : "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>)"
  show "y \<le> x"
  proof (rule dense_le)
    fix z
    assume "z < y"
    then have "0 < y - z"
      by simp
    then have "y \<le> x + (y - z)"
      using h1 by simp
    then have "0 \<le> x - z"
      by simp
    then show "z \<le> x"
      by simp
  qed
qed

(* 4\<ordfeminine> demostración *)
lemma
  fixes x y :: real
  shows "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>) \<longrightarrow> y \<le> x"
  by (simp add: field_le_epsilon)

end

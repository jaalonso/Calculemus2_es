(* CS_de_continuidad.thy
Si f es continua en a y el límite de u(n) es a, entonces el límite de f(u(n)) es f(a)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla,  4-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, se puede definir que a es el límite de la sucesión u
-- por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
--      "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> \<le> \<epsilon>)"
-- y que f es continua en a por
--    definition continua_en :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
--      "continua_en f a \<longleftrightarrow>
--       (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"
--
-- Demostrar que si f es continua en a y el límite de u(n) es a,
-- entonces el límite de f(u(n)) es f(a).
-- ------------------------------------------------------------------ *)

theory CS_de_continuidad
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> \<le> \<epsilon>)"

definition continua_en :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "continua_en f a \<longleftrightarrow>
   (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"

(* 1\<ordfeminine> demostración *)
lemma
  assumes "continua_en f a"
          "limite u a"
  shows "limite (f \<circ> u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain \<delta> where h\<delta>1 : "\<delta> > 0" and
                      h\<delta>2 :" (\<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"
    using assms(1) continua_en_def by auto
  obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - a\<bar> \<le> \<delta>"
    using assms(2) limite_def h\<delta>1 by auto
  have "\<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
  proof (intro allI impI)
    fix n
    assume "n \<ge> k"
    then have "\<bar>u n - a\<bar> \<le> \<delta>"
      using hk by auto
    then show "\<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
      using h\<delta>2 by simp
  qed
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
    by auto
qed

(* 2\<ordfeminine> demostración *)
lemma
  assumes "continua_en f a"
          "limite u a"
  shows "limite (f \<circ> u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain \<delta> where h\<delta>1 : "\<delta> > 0" and
                      h\<delta>2 :" (\<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"
    using assms(1) continua_en_def by auto
  obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - a\<bar> \<le> \<delta>"
    using assms(2) limite_def h\<delta>1 by auto
  have "\<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
    using hk h\<delta>2 by simp
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
    by auto
qed

(* 3\<ordfeminine> demostración *)
lemma
  assumes "continua_en f a"
          "limite u a"
  shows "limite (f \<circ> u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain \<delta> where h\<delta>1 : "\<delta> > 0" and
                      h\<delta>2 :" (\<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"
    using assms(1) continua_en_def by auto
  obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - a\<bar> \<le> \<delta>"
    using assms(2) limite_def h\<delta>1 by auto
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
    using hk h\<delta>2 by auto
qed

(* 4\<ordfeminine> demostración *)
lemma
  assumes "continua_en f a"
          "limite u a"
  shows "limite (f \<circ> u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain \<delta> where
              h\<delta> : "\<delta> > 0 \<and> (\<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"
    using assms(1) continua_en_def by auto
  then obtain k where "\<forall>n\<ge>k. \<bar>u n - a\<bar> \<le> \<delta>"
    using assms(2) limite_def by auto
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
    using h\<delta> by auto
qed

(* 5\<ordfeminine> demostración *)
lemma
  assumes "continua_en f a"
          "limite u a"
  shows "limite (f \<circ> u) (f a)"
  using assms continua_en_def limite_def
  by force

end

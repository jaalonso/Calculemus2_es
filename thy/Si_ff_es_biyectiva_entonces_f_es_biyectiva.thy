(* Si_ff_es_biyectiva_entonces_f_es_biyectiva.thy
-- Si f \<circ> f es biyectiva, entonces f es biyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si f\<sqdot>f es biyectiva, entonces f es biyectiva.
-- ------------------------------------------------------------------ *)

theory Si_ff_es_biyectiva_entonces_f_es_biyectiva
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma
  assumes "bij (f \<circ> f)"
  shows   "bij f"
proof (rule bijI)
  show "inj f"
  proof -
    have h1 : "inj (f \<circ> f)"
      using assms by (simp only: bij_is_inj)
    then show "inj f"
      by (simp only: inj_on_imageI2)
  qed
next
  show "surj f"
  proof -
    have h2 : "surj (f \<circ> f)"
      using assms by (simp only: bij_is_surj)
    then show "surj f"
      by auto
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma
  assumes "bij (f \<circ> f)"
  shows   "bij f"
proof (rule bijI)
  show "inj f"
    using assms bij_is_inj inj_on_imageI2 
    by blast
next
  show "surj f"
    using assms bij_is_surj 
    by fastforce
qed

(* 3 demostración *)
lemma
  assumes "bij (f \<circ> f)"
  shows   "bij f"
by (metis assms 
          bij_betw_comp_iff 
          bij_betw_def 
          bij_betw_imp_surj 
          inj_on_imageI2)

end

(* Praeclarum_theorema.thy
-- Praeclarum theorema
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-enero-2025
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar el [praeclarum theorema](https://tinyurl.com/25yt3ef9) de
-- Leibniz:
--    (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s))
-- ------------------------------------------------------------------ *)

theory Praeclarum_theorema
imports Main
begin

(* 1\<ordfeminine> demostración: detallada *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
proof (rule impI)
  assume "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)"
  show "(p \<and> r) \<longrightarrow> (q \<and> s)"
  proof (rule impI)
    assume "p \<and> r"
    show "q \<and> s"
    proof (rule conjI)
      have "p \<longrightarrow> q" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> by (rule conjunct1)
      moreover have "p" using \<open>p \<and> r\<close> by (rule conjunct1)
      ultimately show "q" by (rule mp)
    next
      have "r \<longrightarrow> s" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> by (rule conjunct2)
      moreover have "r" using \<open>p \<and> r\<close> by (rule conjunct2)
      ultimately show "s" by (rule mp)
    qed
  qed
qed

(* 2\<ordfeminine> demostración: estructurada *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
proof
  assume "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)"
  show "(p \<and> r) \<longrightarrow> (q \<and> s)"
  proof
    assume "p \<and> r"
    show "q \<and> s"
    proof
      have "p \<longrightarrow> q" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> ..
      moreover have "p" using \<open>p \<and> r\<close> ..
      ultimately show "q" ..
    next
      have "r \<longrightarrow> s" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> ..
      moreover have "r" using \<open>p \<and> r\<close> ..
      ultimately show "s" ..
    qed
  qed
qed

(* 3\<ordfeminine> demostración: aplicativa *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
  apply (rule impI)
  apply (rule impI)
  apply (erule conjE)+
  apply (rule conjI)
   apply (erule mp)
   apply assumption
  apply (erule mp)
  apply assumption
  done

(* 4\<ordfeminine> demostración: automática *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
  by simp

end

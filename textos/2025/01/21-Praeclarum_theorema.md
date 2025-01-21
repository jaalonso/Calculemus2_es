---
title: Praeclarum theorema
date: 2025-01-21 06:00:00 UTC+02:00
category: Proposicional
has_math: true
---

---

Demostrar con Lean4 y con Isabelle/HOL el [Praeclarum theorema](https://tinyurl.com/25yt3ef9) de Leibniz:
\\[ (p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s)) \\]


---

<!-- TEASER_END -->
# Demostraciones

A continuación se muestran las [demostraciones con Lean4](#lean) y las [demostraciones con Isabelle/HOL](#isabelle).

<a name="lean"></a>
## 1. Demostraciones con Lean4

~~~lean
import Mathlib.Tactic

variable (p q r s : Prop)

-- 1ª demostración
-- ===============

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
by
  intro ⟨hpq, hrs⟩ ⟨hp, hr⟩
  -- hpq : p → q
  -- hrs : r → s
  -- hp : p
  -- hr : r
  constructor
  . -- q
    exact hpq hp
  . -- s
    exact hrs hr

-- 2ª demostración
-- ===============

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
by
  intro ⟨hpq, hrs⟩ ⟨hp, hr⟩
  -- hpq : p → q
  -- hrs : r → s
  -- hp : p
  -- hr : r
  exact ⟨hpq hp, hrs hr⟩

-- 3ª demostración
-- ===============

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
fun ⟨hpq, hrs⟩ ⟨hp, hr⟩ ↦ ⟨hpq hp, hrs hr⟩

-- 4ª demostración
-- ===============

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
fun ⟨hpq, hrs⟩ hpr ↦ And.imp hpq hrs hpr

-- 5ª demostración
-- ===============

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
by aesop
~~~

<a name="isabelle"></a>
## 2. Demostraciones con Isabelle/HOL

~~~isabelle
theory Praeclarum_theorema
imports Main
begin

(* 1ª demostración: detallada *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
proof (rule impI)
  assume "(p ⟶ q) ∧ (r ⟶ s)"
  show "(p ∧ r) ⟶ (q ∧ s)"
  proof (rule impI)
    assume "p ∧ r"
    show "q ∧ s"
    proof (rule conjI)
      have "p ⟶ q" using ‹(p ⟶ q) ∧ (r ⟶ s)› by (rule conjunct1)
      moreover have "p" using ‹p ∧ r› by (rule conjunct1)
      ultimately show "q" by (rule mp)
    next
      have "r ⟶ s" using ‹(p ⟶ q) ∧ (r ⟶ s)› by (rule conjunct2)
      moreover have "r" using ‹p ∧ r› by (rule conjunct2)
      ultimately show "s" by (rule mp)
    qed
  qed
qed

(* 2ª demostración: estructurada *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
proof
  assume "(p ⟶ q) ∧ (r ⟶ s)"
  show "(p ∧ r) ⟶ (q ∧ s)"
  proof
    assume "p ∧ r"
    show "q ∧ s"
    proof
      have "p ⟶ q" using ‹(p ⟶ q) ∧ (r ⟶ s)› ..
      moreover have "p" using ‹p ∧ r› ..
      ultimately show "q" ..
    next
      have "r ⟶ s" using ‹(p ⟶ q) ∧ (r ⟶ s)› ..
      moreover have "r" using ‹p ∧ r› ..
      ultimately show "s" ..
    qed
  qed
qed

(* 3ª demostración: aplicativa *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
  apply (rule impI)
  apply (rule impI)
  apply (erule conjE)+
  apply (rule conjI)
   apply (erule mp)
   apply assumption
  apply (erule mp)
  apply assumption
  done

(* 4ª demostración: automática *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
  by simp

end
~~~

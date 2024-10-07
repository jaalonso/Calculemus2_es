---
title: Principio del palomar
date: 2024-10-07 06:00:00 UTC+02:00
category: Conjuntos finitos
has_math: true
---

Demostrar con Lean4 el [principio del palomar](https://tinyurl.com/kobfceg); decir, que si \\(S\\) es un conjunto finito y \\(T\\) y \\(U\\) son subconjuntos de \\(S\\) tales que el número de elementos de \\(S\\) es menor que la suma del número de elementos de \\(T\\) y \\(U\\), entonces la intersección de \\(T\\) y \\(U\\) es no vacía.

Para ello, completar la siguiente teoría de Lean4:

~~~lean
import Mathlib.Data.Finset.Card

open Finset

variable [DecidableEq α]
variable {s t u : Finset α}

-- 1ª demostración
-- ===============

example
  (hts : t ⊆ s)
  (hus : u ⊆ s)
  (hstu : card s < card t + card u)
  : Finset.Nonempty (t ∩ u) :=
by sorry
~~~
<!-- TEASER_END -->

# 1. Demostración en lenguaje natural

Se demuestra por contraposición. Para ello, se supone que
\\[ T ∩ U = ∅ \\tag{1} \\]
y hay que demostrar que
\\[ \\text{card}(T) + \\text{card}(U) ≤ \\text{card}(S) \\tag{2} \\]

La desigualdad (2) se demuestra mediante la siguiente cadena de relaciones:
\\begin{align}
   \\text{card}(T) + \\text{card}(U) &= \\text{card}(T ∪ U) + \\text{card}(T ∩ U) \\newline
                     &= \\text{card}(T ∪ U) + 0           &&\\text{[por (1)]} \\newline
                     &= \\text{card}(T ∪ U)               \\newline
                     &≤ \\text{card}(S)                   &&\\text{[porque \\(T ⊆ S\\) y \\(U ⊆ S\\)]}
\\end{align}

# 2. Demostraciones con Lean4

~~~lean
import Mathlib.Data.Finset.Card

open Finset

variable [DecidableEq α]
variable {s t u : Finset α}

set_option pp.fieldNotation false

-- 1ª demostración
-- ===============

example
  (hts : t ⊆ s)
  (hus : u ⊆ s)
  (hstu : card s < card t + card u)
  : Finset.Nonempty (t ∩ u) :=
by
  contrapose! hstu
  -- hstu : ¬Finset.Nonempty (t ∩ u)
  -- ⊢ card t + card u ≤ card s
  have h1 : t ∩ u = ∅ := not_nonempty_iff_eq_empty.mp hstu
  have h2 : card (t ∩ u) = 0 := card_eq_zero.mpr h1
  calc
    card t + card u
      = card (t ∪ u) + card (t ∩ u) := (card_union_add_card_inter t u).symm
    _ = card (t ∪ u) + 0            := congrArg (card (t ∪ u) + .) h2
    _ = card (t ∪ u)                := add_zero (card (t ∪ u))
    _ ≤ card s                      := card_le_card (union_subset hts hus)

-- 2ª demostración
-- ===============

example
  (hts : t ⊆ s)
  (hus : u ⊆ s)
  (hstu : card s < card t + card u)
  : Finset.Nonempty (t ∩ u) :=
by
  contrapose! hstu
  -- hstu : ¬Finset.Nonempty (t ∩ u)
  -- ⊢ card t + card u ≤ card s
  calc
    card t + card u
      = card (t ∪ u) + card (t ∩ u) :=
          (card_union_add_card_inter t u).symm
    _ = card (t ∪ u) + 0 :=
          congrArg (card (t ∪ u) + .) (card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hstu))
    _ = card (t ∪ u) :=
          add_zero (card (t ∪ u))
    _ ≤ card s :=
          card_le_card (union_subset hts hus)

-- 3ª demostración
-- ===============

example
  (hts : t ⊆ s)
  (hus : u ⊆ s)
  (hstu : card s < card t + card u)
  : Finset.Nonempty (t ∩ u) :=
by
  contrapose! hstu
  -- hstu : ¬Finset.Nonempty (t ∩ u)
  -- ⊢ card t + card u ≤ card s
  calc
    card t + card u
      = card (t ∪ u) := by simp [← card_union_add_card_inter,
                                 not_nonempty_iff_eq_empty.1 hstu]
    _ ≤ card s       := by gcongr; exact union_subset hts hus

-- 4ª demostración
-- ===============

example
  (hts : t ⊆ s)
  (hus : u ⊆ s)
  (hstu : card s < card t + card u)
  : Finset.Nonempty (t ∩ u) :=
inter_nonempty_of_card_lt_card_add_card hts hus hstu

-- Lemas usados
-- ============

-- variable (a : ℕ)
-- #check (add_zero a : a + 0 = a)
-- #check (card_eq_zero : card s = 0 ↔ s = ∅)
-- #check (card_le_card : s ⊆ t → card s ≤ card t)
-- #check (card_union_add_card_inter s t : card (s ∪ t) + card (s ∩ t) =card s + card t)
-- #check (inter_nonempty_of_card_lt_card_add_card : t ⊆ s → u ⊆ s → card s < card t + card u → Finset.Nonempty (t ∩ u))
-- #check (not_nonempty_iff_eq_empty : ¬Finset.Nonempty s ↔ s = ∅)
-- #check (union_subset : s ⊆ u → t ⊆ u → s ∪ t ⊆ u)
~~~

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Principio_del_palomar.lean).

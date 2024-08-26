---
title: Pruebas de take n xs ++ drop n xs = xs
date: 2024-08-14 06:00:00 UTC+02:00
category: Listas
has_math: true
---

[mathjax]

En Lean4, las funciones

    take : Nat → List α → Nat
    drop : Nat → List α → Nat
    (++) : List α → List α → List α

estan definas tales que

+ (take n xs) es la lista formada por los n primeros elementos de xs. Por ejemplo,

        take 2 [3,5,1,9,7] = [3,5]

+ (drop n xs) es la lista obtenida borrando los n primeros elementos de xs. Por ejemplo,

        drop 2 [3,5,1,9,7] = [1,9,7]

+ (xs ++ ys) es la lista obtenida concatenando xs e ys. Por ejemplo,

        [3,5] ++ [1,9,7] = [3,5,1,9,7]

Estas funciones se caracterizan por los siguientes lemas

    take_zero      : take 0 xs = []
    take_nil       : take n [] = []
    take_cons      : take (succ n) (x :: xs) = x :: take n xs
    drop_zero      : drop 0 xs = xs
    drop_nil       : drop n [] = []
    drop_succ_cons : drop (n + 1) (x :: xs) = drop n xs
    nil_append     : [] ++ ys = ys
    cons_append    : (x :: xs) ++ y = x :: (xs ++ ys)

Demostrar que

    take n xs ++ drop n xs = xs

Para ello, completar la siguiente teoría:

<pre lang="lean">
import Mathlib.Data.List.Basic
import Mathlib.Tactic
open List Nat

variable {α : Type}
variable (n : ℕ)
variable (x : α)
variable (xs : List α)

example : take n xs ++ drop n xs = xs :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que

    (∀ n)(∀ xs)[take n xs ++ drop n xs = xs]

Lo haremos por inducción en n.

Caso base: Sea n = 0. Tenemos que probar que

    (∀ xs)[take n xs ++ drop n xs = xs]

Sea xs cualquier lista. Entonces,

    take n xs ++ drop n xs = take 0 xs ++ drop 0 xs
                           = [] ++ xs
                           = xs

Paso de inducción: Supongamos la hipótesis de inducción (HI):

    (∀ xs)[take n xs ++ drop n xs = xs]

y tenemos que probar que

    (∀ xs)[take (n+1) xs ++ drop (n+1) xs = xs]

Lo demostraremos por casos sobre exs.

Primer caso: Supongamos que xs = []. Entonces,

    take (n+1) xs ++ drop (n+1) xs = take (n+1) [] ++ drop (n+1) []
                                   = [] ++ []
                                   = []

Segundo caso: Supongamos que xs = y :: ys. Entonces,

    take (n+1) xs ++ drop (n+1) xs
    = take (n+1) (y :: ys) ++ drop (n+1) (y :: ys)
    = (y :: take n ys) ++ drop n ys
    = y :: (take n ys ++ drop n ys)
    = y :: ys                                          [by HI]
    = xs

Otra forma de demostrarlo es ditinguiendo los tres casos de la definicón de take; que es

    take n xs = [],             if n = 0
              = [],             if n = m+1 and xs = []
              = y :: take m ys, if n = m+1 and xs = y :: ys

Caso 1: Supogamos que n = 0. Entonces,

    take n xs ++ drop n xs = take 0 xs ++ drop 0 xs
                           = [] ++ xs
                           = xs

Caso 2: Supongamos que n = m+1 y xs = []. Entonces,

    take (m+1) xs ++ drop (m+1) xs = take (m+1) [] ++ drop (m+1) []
                                   = [] ++ []
                                   = []

Caso 3: Supongamos que n = m+1 y xs = y :: ys. Entonces,

    take (m+1) xs ++ drop (m+1) xs
    = take (m+1) (y :: ys) ++ drop (m+1) (y :: ys)
    = (y :: take m ys) ++ drop m ys
    = y :: (take m ys ++ drop m ys)
    = y :: ys                       [by the lemma applied to m and ys]
    = xs

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.List.Basic
import Mathlib.Tactic
open List Nat

variable {α : Type}
variable (n : ℕ)
variable (x : α)
variable (xs : List α)

-- Demostración 1
-- ==============

example : take n xs ++ drop n xs = xs :=
by
  induction' n with n HI generalizing xs
  . -- ⊢ take zero xs ++ drop zero xs = xs
    calc take zero xs ++ drop zero xs
           = [] ++ xs                 := rfl
         _ = xs                       := rfl
  . -- n : ℕ
    -- HI : ∀ (xs : List α), take n xs ++ drop n xs = xs
    -- xs : List α
    -- ⊢ take (succ n) xs ++ drop (succ n) xs = xs
    cases' xs with y ys
    . -- ⊢ take (succ n) [] ++ drop (succ n) [] = []
      calc take (succ n) [] ++ drop (succ n) []
             = [] ++ [] := rfl
           _ = []       := by rfl
    . -- y : α
      -- ys : List α
      -- ⊢ take (n+1) (y :: ys) ++ drop (n+1) (y :: ys) = y :: ys
      calc
        take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
          = (y :: take n ys) ++ drop n ys := rfl
        _ = y :: (take n ys ++ drop n ys) := rfl
        _ = y :: ys                       := by rw [HI]

-- Demostración 2
-- ==============

example : take n xs ++ drop n xs = xs :=
by
  induction' n with n HI generalizing xs
  . -- ⊢ take zero xs ++ drop zero xs = xs
    rfl
  . -- n : ℕ
    -- HI : ∀ (xs : List α), take n xs ++ drop n xs = xs
    -- xs : List α
    -- ⊢ take (succ n) xs ++ drop (succ n) xs = xs
    cases' xs with y ys
    . -- ⊢ take (succ n) [] ++ drop (succ n) [] = []
      rfl
    . -- y : α
      -- ys : List α
      -- ⊢ take (n+1) (y :: ys) ++ drop (n+1) (y :: ys) = y :: ys
      calc
        take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
          = y :: (take n ys ++ drop n ys) := rfl
        _ = y :: ys                       := by rw [HI]

-- demostración 3
-- ==============

lemma take_drop_1 : ∀ (n : Nat) (xs : List α), take n xs ++ drop n xs = xs
  | 0, xs =>
    -- ⊢ take 0 xs ++ drop 0 xs = xs
    calc
      take 0 xs ++ drop 0 xs
        = [] ++ xs := rfl
      _ = xs       := rfl
  | n+1, [] =>
    -- ⊢ take (n + 1) [] ++ drop (n + 1) [] = []
    calc
      take (n+1) [] ++ drop (n+1) []
        = [] ++ [] := rfl
      _ = []       := by rfl
  | n+1, y :: ys =>
    -- ⊢ take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys) = y :: ys
    calc
      take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
        = (y :: take n ys) ++ drop n ys := rfl
      _ = y :: (take n ys ++ drop n ys) := rfl
      _ = y :: ys                       := by rw [take_drop_1 n ys]

-- Demostración 4
-- ==============

lemma take_drop_2 : ∀ (n : Nat) (xs : List α), take n xs ++ drop n xs = xs
  | 0, _ =>
    -- ⊢ take 0 xs ++ drop 0 xs = xs
    rfl
  | _+1, [] =>
    -- ⊢ take (n + 1) [] ++ drop (n + 1) [] = []
    rfl
  | n+1, y :: ys =>
    -- ⊢ take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys) = y :: ys
    calc
      take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
      _ = y :: (take n ys ++ drop n ys) := rfl
      _ = y :: ys                       := by rw [take_drop_2 n ys]

-- Demostración 5
-- ==============

lemma take_drop_3 : take n xs ++ drop n xs = xs :=
take_append_drop n xs
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Pruebas_de_take_n_xs_++_drop_n_xs_Ig_xs.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory "Proofs_of_take_n_xs_++_drop_n_xs_Eq_xs"
imports Main
begin

fun take' :: "nat ⇒ 'a list ⇒ 'a list" where
  "take' n []           = []"
| "take' 0 xs           = []"
| "take' (Suc n) (x#xs) = x # (take' n xs)"

fun drop' :: "nat ⇒ 'a list ⇒ 'a list" where
  "drop' n []           = []"
| "drop' 0 xs           = xs"
| "drop' (Suc n) (x#xs) = drop' n xs"

(* Demostración 1 *)

lemma "take' n xs @ drop' n xs = xs"
proof (induct rule: take'.induct)
  fix n
  have "take' n [] @ drop' n [] = [] @ drop' n []"
    by (simp only: take'.simps(1))
  also have "… = drop' n []"
    by (simp only: append.simps(1))
  also have "… = []"
    by (simp only: drop'.simps(1))
  finally show "take' n [] @ drop' n [] = []"
    by this
next
  fix x :: 'a and xs :: "'a list"
  have "take' 0 (x#xs) @ drop' 0 (x#xs) =
        [] @ drop' 0 (x#xs)"
    by (simp only: take'.simps(2))
  also have "… = drop' 0 (x#xs)"
    by  (simp only: append.simps(1))
  also have "… = x # xs"
    by  (simp only: drop'.simps(2))
  finally show "take' 0 (x#xs) @ drop' 0 (x#xs) = x#xs"
    by this
next
  fix n :: nat and x :: 'a and xs :: "'a list"
  assume HI: "take' n xs @ drop' n xs = xs"
  have "take' (Suc n) (x # xs) @ drop' (Suc n) (x # xs) =
        (x # (take' n xs)) @ drop' n xs"
    by (simp only: take'.simps(3)
                   drop'.simps(3))
  also have "… = x # (take' n xs @ drop' n xs)"
    by (simp only: append.simps(2))
  also have "… = x#xs"
    by (simp only: HI)
  finally show "take' (Suc n) (x#xs) @ drop' (Suc n) (x#xs) =
                x#xs"
    by this
qed

(* Demostración 2 *)

lemma "take' n xs @ drop' n xs = xs"
proof (induct rule: take'.induct)
case (1 n)
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by simp
next
  case (3 n x xs)
  then show ?case by simp
qed

(* Demostración 3 *)

lemma "take' n xs @ drop' n xs = xs"
by (induct rule: take'.induct) simp_all

end
</pre>

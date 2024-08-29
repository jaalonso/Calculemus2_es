---
title: Pruebas de equivalencia de definiciones de la función de Fibonacci
date: 2024-08-29 06:00:00 UTC+02:00
category: Inducción
has_math: true
---

[mathjax]

En Lean4, se puede definir la función de Fibonacci por
<pre lang="haskell">
   def fibonacci : Nat → Nat
     | 0     => 0
     | 1     => 1
     | n + 2 => fibonacci n + fibonacci (n+1)
</pre>

Otra definición más eficiente es
<pre lang="haskell">
   def fib (n : Nat) : Nat :=
     (aux n).1
   where
     aux : Nat → Nat × Nat
       | 0   => (0, 1)
       | n + 1 =>
         let p := aux n
         (p.2, p.1 + p.2)
</pre>

Demostrar que ambas definiciones son equivalentes; es decir,
<pre lang="haskell">
   fibonacci = fib
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
open Nat

-- Para que no use la notación con puntos
set_option pp.fieldNotation false

def fibonacci : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibonacci n + fibonacci (n+1)

def fib (n : Nat) : Nat :=
  (aux n).1
where
  aux : Nat → Nat × Nat
    | 0   => (0, 1)
    | n + 1 =>
      let p := aux n
      (p.2, p.1 + p.2)

example : fibonacci = fib :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

En la demostración usaremos el siguiente lema auxiliar
<pre lang="haskell">
   fib_suma (n : Nat) : fib (n + 2) = fib n + fib (n + 1)
</pre>

Tenemos que demostrar que, para todo n ∈ ℕ,
<pre lang="haskell">
   fibonacci n = fib n
</pre>
Lo probaremos por inducción en n.

**Caso 1**: Supongamos que n = 0. Entonces,

    fibonacci n = fibonacci 0
                = 1

y

    fib n = fib 0
          = (aux 0).1
          = (0, 1).1
          = 1

Por tanto,

    fibonacci n = fib n

**Caso 2**: Supongamos que n = 1. Entonces,

    fibonacci n = 1

y

    fib 1 = (aux 1).1
          = (p.2, p.1 + p.2).1
            donde p = aux 0
          = ((0, 1).2, (0, 1).1 + (0, 1).2).1
          = (1, 0 + 1).1
          = 1

**Caso 3**: Supongamos que n = m + 2 y que se verifica las hipótesis de inducción,
<pre lang="haskell">
   HI1 : fibonacci n = fib n
   HI2 : fibonacci (n + 1) = fib (n + 1)
</pre>

Entonces,

    fibonacci n
    = fibonacci (m + 2)
    = fibonacci m + fibonacci (m + 1)
    = fib m + fib (m + 1)                [por HI1, HI2]
    = fib (m + 2)                        [por fib_suma]
    = fib n

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
open Nat

-- Para que no use la notación con puntos
set_option pp.fieldNotation false

def fibonacci : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibonacci n + fibonacci (n+1)

def fib (n : Nat) : Nat :=
  (aux n).1
where
  aux : Nat → Nat × Nat
    | 0   => (0, 1)
    | n + 1 =>
      let p := aux n
      (p.2, p.1 + p.2)

-- Lema auxiliar
-- =============

theorem fib_suma (n : Nat) : fib (n + 2) = fib n + fib (n + 1) :=
by rfl

-- 1ª demostración
-- ===============

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n HI1 HI2 =>
    -- n : Nat
    -- HI1 : fibonacci n = fib n
    -- HI2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    rw [fib_suma]
    -- ⊢ fibonacci (succ (succ n)) = fib n + fib (n + 1)
    rw [fibonacci]
    -- ⊢ fibonacci n + fibonacci (n + 1) = fib n + fib (n + 1)
    rw [HI1]
    -- ⊢ fib n + fibonacci (n + 1) = fib n + fib (n + 1)
    rw [HI2]

-- 2ª demostración
-- ===============

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n HI1 HI2 =>
    -- n : Nat
    -- HI1 : fibonacci n = fib n
    -- HI2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    calc fibonacci (succ (succ n))
         = fibonacci n + fibonacci (n + 1) := by rw [fibonacci]
       _ = fib n + fib (n + 1)             := by rw [HI1, HI2]
       _ = fib (succ (succ n))             := by rw [fib_suma]

-- 3ª demostración
-- ===============

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n HI1 HI2 =>
    -- n : Nat
    -- HI1 : fibonacci n = fib n
    -- HI2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    simp [HI1, HI2, fibonacci, fib_suma]
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Fibonacci.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Fibonacci
imports Main
begin

fun fibonacci :: "nat ⇒ nat"
  where
    "fibonacci 0 = 0"
  | "fibonacci (Suc 0) = 1"
  | "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"

fun fibAux :: "nat => nat × nat"
  where
     "fibAux 0 = (0, 1)"
   | "fibAux (Suc n) = (snd (fibAux n), fst (fibAux n) + snd (fibAux n))"

definition fib :: "nat ⇒ nat" where
  "fib n = (fst (fibAux n))"

lemma "fibonacci n = fib n"
proof (induct n rule: fibonacci.induct)
  show "fibonacci 0 = fib 0"
    by (simp add: fib_def)
next
  show "fibonacci (Suc 0) = fib (Suc 0)"
    by (simp add: fib_def)
next
  fix n
  assume HI1 : "fibonacci n = fib n"
  assume HI2 : "fibonacci (Suc n) = fib (Suc n)"
  have "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"
    by simp
  also have "… = fib n + fib (Suc n)"
    by (simp add: HI1 HI2)
  also have "… = fib (Suc (Suc n))"
    by (simp add: fib_def)
  finally show "fibonacci (Suc (Suc n)) = fib (Suc (Suc n))"
    by this
qed

end
</pre>

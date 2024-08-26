---
title: Pruebas de que la función espejo de los árboles binarios es involutiva
date: 2024-08-26 06:00:00 UTC+02:00
category: Árboles binarios
has_math: true
---

[mathjax]

El árbol correspondiente a

        3
       / \
      2   4
     / \
    1   5

se puede representar por el término

    nodo 3 (nodo 2 (hoja 1) (hoja 5)) (hoja 4)

usado el tipo de dato arbol definido por
<pre lang="lean">
   inductive arbol (α : Type) : Type
   | hoja : α → arbol
   | nodo : α → arbol → arbol → arbol
</pre>

La imagen especular del árbol anterior es

      3
     / \
    4   2
       / \
      5   1

cuyo término es

    nodo 3 (hoja 4) (nodo 2 (hoja 5) (hoja 1))

La definición de la función que calcula la imagen especular es
<pre lang="lean">
   def espejo : arbol α → arbol α
   | (hoja x)     := hoja x
   | (nodo x i d) := nodo x (espejo d) (espejo i)
</pre>

Demostrar que la función espejo es involutiva; es decir,
<pre lang="lean">
   espejo (espejo a) = a
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable {α : Type}

-- Para que no use la notación con puntos
set_option pp.fieldNotation false

inductive Arbol (α : Type) : Type
  | hoja : α → Arbol α
  | nodo : α → Arbol α → Arbol α → Arbol α

namespace Arbol

variable (a i d : Arbol α)
variable (x : α)

def espejo : Arbol α → Arbol α
  | (hoja x)     => hoja x
  | (nodo x i d) => nodo x (espejo d) (espejo i)

example :
  espejo (espejo a) = a :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

De la definición de la función espejo se obtienen los siguientes lemas
<pre lang="lean">
   espejo1 : espejo (hoja x) = hoja x
   espejo2 : espejo (nodo x i d) = nodo x (espejo d) (espejo i)
</pre>

Demostraremos que, para todo árbol a,

    espejo (espejo a) = a

por inducción sobre a.

Caso base: Supongamos que a = hoja x. Entonces,

    espejo (espejo a)
    = espejo (espejo (hoja x))
    = espejo (hoja x)             [por espejo1]
    = hoja x                      [por espejo1]
    = a

Paso de inducción: Supongamos que a = nodo x i d y se cumplen las hipótesis de inducción

    espejo (espejo i) = i                                         (Hi)
    espejo (espejo d) = d                                         (Hi)

Entonces,

    espejo (espejo a)
    = espejo (espejo (nodo x i d))
    = espejo (nodo x (espejo d) (espejo i))             [por espejo2]
    = nodo x (espejo (espejo i)) (espejo (espejo d))    [por espejo2]
    = nodo x i (espejo (espejo d))                      [por Hi]
    = nodo x i d                                        [por Hd]
    = a

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Pruebas_de_que_la_funcion_espejo_de_los_arboles_binarios_es_involutiva.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Pruebas_de_que_la_funcion_espejo_de_los_arboles_binarios_es_involutiva
imports Main
begin

datatype 'a arbol = hoja "'a"
                  | nodo "'a" "'a arbol" "'a arbol"

fun espejo :: "'a arbol ⇒ 'a arbol" where
  "espejo (hoja x)     = (hoja x)"
| "espejo (nodo x i d) = (nodo x (espejo d) (espejo i))"

(* 1ª demostración *)
lemma
  fixes a :: "'b arbol"
  shows "espejo (espejo a) = a" (is "?P a")
proof (induct a)
  fix x
  show "?P (hoja x)"
    by (simp only: espejo.simps(1))
next
  fix x
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (nodo x i d)"
  proof -
    have "espejo (espejo (nodo x i d)) =
          espejo (nodo x (espejo d) (espejo i))"
      by (simp only: espejo.simps(2))
    also have "… = nodo x (espejo (espejo i)) (espejo (espejo d))"
      by (simp only: espejo.simps(2))
    also have "… = nodo x i d"
      by (simp only: h1 h2)
    finally show ?thesis
      by this
 qed
qed

(* 2ª demostración *)
lemma
  fixes a :: "'b arbol"
  shows "espejo (espejo a) = a" (is "?P a")
proof (induct a)
  fix x
  show "?P (hoja x)"  by simp
next
  fix x
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (nodo x i d)"
  proof -
    have "espejo (espejo (nodo x i d)) =
          espejo (nodo x (espejo d) (espejo i))" by simp
    also have "… = nodo x (espejo (espejo i)) (espejo (espejo d))"
      by simp
    also have "… = nodo x i d" using h1 h2 by simp
    finally show ?thesis .
 qed
qed

(* 3ª demostración *)
lemma
  "espejo (espejo a ) = a"
by (induct a) simp_all

end
</pre>

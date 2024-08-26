(* Pruebas_de_que_la_funcion_espejo_de_los_arboles_binarios_es_involutiva.thy
-- Pruebas de que la función espejo de los árboles binarios es involutiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-agosto-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- El árbol correspondiente a
--        3
--       / \
--      2   4
--     / \
--    1   5
-- se puede representar por el término
--    nodo 3 (nodo 2 (hoja 1) (hoja 5)) (hoja 4)
-- usado el tipo de dato arbol definido por
--    datatype 'a arbol = hoja "'a"
--                      | nodo "'a" "'a arbol" "'a arbol"
--
-- La imagen especular del árbol anterior es
--      3
--     / \
--    4   2
--       / \
--      5   1
-- cuyo término es
--    nodo 3 (hoja 4) (nodo 2 (hoja 5) (hoja 1))
--
-- La definición de la función que calcula la imagen especular es
--    fun espejo :: "'a arbol ⇒ 'a arbol" where
--      "espejo (hoja x)     = (hoja x)"
--    | "espejo (nodo x i d) = (nodo x (espejo d) (espejo i))"
--
-- Demostrar que la función espejo es involutiva; es decir,
--    espejo (espejo a) = a
-- ------------------------------------------------------------------ *)

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

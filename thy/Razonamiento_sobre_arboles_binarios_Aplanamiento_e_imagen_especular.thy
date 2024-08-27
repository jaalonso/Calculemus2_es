(* Razonamiento_sobre_arboles_binarios_Aplanamiento_e_imagen_especular.thy
-- Pruebas de aplana (espejo a) = reverse (aplana a).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-agosto-2024
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
-- usando el tipo de dato arbol definido por
--    datatype 'a arbol = hoja "'a"
--                      | nodo "'a" "'a arbol" "'a arbol"
--
-- La imagen especular del árbol anterior es
--      3
--     / \
--    4   2
--       / \
--      5   1
-- y la lista obtenida aplanándolo (recorriéndolo en orden infijo) es
--    [4, 3, 5, 2, 1]
--
-- La definición de la función que calcula la imagen especular es
--    fun espejo :: "'a arbol \<Rightarrow> 'a arbol" where
--      "espejo (hoja x)     = (hoja x)"
--    | "espejo (nodo x i d) = (nodo x (espejo d) (espejo i))"
-- y la que aplana el árbol es
--    fun aplana :: "'a arbol \<Rightarrow> 'a list" where
--      "aplana (hoja x)     = [x]"
--    | "aplana (nodo x i d) = (aplana i) @ [x] @ (aplana d)"
--
-- Demostrar que
--    aplana (espejo a) = rev (aplana a)
-- ------------------------------------------------------------------ *)

theory Razonamiento_sobre_arboles_binarios_Aplanamiento_e_imagen_especular
imports Main
begin

datatype 'a arbol = hoja "'a"
                  | nodo "'a" "'a arbol" "'a arbol"

fun espejo :: "'a arbol \<Rightarrow> 'a arbol" where
  "espejo (hoja x)     = (hoja x)"
| "espejo (nodo x i d) = (nodo x (espejo d) (espejo i))"

fun aplana :: "'a arbol \<Rightarrow> 'a list" where
  "aplana (hoja x)     = [x]"
| "aplana (nodo x i d) = (aplana i) @ [x] @ (aplana d)"

(* Lema auxiliar *)
(* ============= *)

(* 1\<ordfeminine> demostración del lema auxiliar *)
lemma "rev [x] = [x]"
proof -
  have "rev [x] = rev [] @ [x]"
    by (simp only: rev.simps(2))
  also have "\<dots> = [] @ [x]"
    by (simp only: rev.simps(1))
  also have "\<dots> = [x]"
    by (simp only: append.simps(1))
  finally show ?thesis
    by this
qed

(* 2\<ordfeminine> demostración del lema auxiliar *)
lemma rev_unit: "rev [x] = [x]"
by simp

(* Lema principal *)
(* ============== *)

(* 1\<ordfeminine> demostración *)
lemma
  fixes a :: "'b arbol"
  shows "aplana (espejo a) = rev (aplana a)" (is "?P a")
proof (induct a)
  fix x :: 'b
  have "aplana (espejo (hoja x)) = aplana (hoja x)"
    by (simp only: espejo.simps(1))
  also have "\<dots> = [x]"
    by (simp only: aplana.simps(1))
  also have "\<dots> = rev [x]"
    by (rule rev_unit [symmetric])
  also have "\<dots> = rev (aplana (hoja x))"
    by (simp only: aplana.simps(1))
  finally show "?P (hoja x)"
    by this
next
  fix x :: 'b
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (nodo x i d)"
  proof -
    have "aplana (espejo (nodo x i d)) =
          aplana (nodo x (espejo d) (espejo i))"
      by (simp only: espejo.simps(2))
    also have "\<dots> = (aplana (espejo d)) @ [x] @ (aplana (espejo i))"
      by (simp only: aplana.simps(2))
    also have "\<dots> = (rev (aplana d)) @ [x] @ (rev (aplana i))"
      by (simp only: h1 h2)
    also have "\<dots> = rev ((aplana i) @ [x] @ (aplana d))"
      by (simp only: rev_append rev_unit append_assoc)
    also have "\<dots> = rev (aplana (nodo x i d))"
      by (simp only: aplana.simps(2))
    finally show ?thesis
      by this
 qed
qed

(* 2\<ordfeminine> demostración *)
lemma
  fixes a :: "'b arbol"
  shows "aplana (espejo a) = rev (aplana a)" (is "?P a")
proof (induct a)
  fix x
  show "?P (hoja x)" by simp
next
  fix x
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (nodo x i d)"
  proof -
    have "aplana (espejo (nodo x i d)) =
          aplana (nodo x (espejo d) (espejo i))" by simp
    also have "\<dots> = (aplana (espejo d)) @ [x] @ (aplana (espejo i))"
      by simp
    also have "\<dots> = (rev (aplana d)) @ [x] @ (rev (aplana i))"
      using h1 h2 by simp
    also have "\<dots> = rev ((aplana i) @ [x] @ (aplana d))" by simp
    also have "\<dots> = rev (aplana (nodo x i d))" by simp
    finally show ?thesis .
 qed
qed

(* 3\<ordfeminine> demostración *)
lemma "aplana (espejo a) = rev (aplana a)"
proof (induct a)
case (hoja x)
then show ?case by simp
next
  case (nodo x i d)
  then show ?case by simp
qed

(* 4\<ordfeminine> demostración *)
lemma "aplana (espejo a) = rev (aplana a)"
  by (induct a) simp_all

end

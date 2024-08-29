-- Razonamiento_sobre_arboles_binarios_Aplanamiento_e_imagen_especular.lean
-- Pruebas de aplana (espejo a) = reverse (aplana a).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-agosto-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- El árbol correspondiente a
--        3
--       / \
--      2   4
--     / \
--    1   5
-- se puede representar por el término
--    Nodo 3 (Nodo 2 (Hoja 1) (Hoja 5)) (Hoja 4)
-- usando el tipo de dato arbol definido por
--    inductive Arbol (α : Type) : Type
--      | Hoja : α → Arbol α
--      | Nodo : α → Arbol α → Arbol α → Arbol α
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
--    def espejo : Arbol α → Arbol α
--      | Hoja x     => Hoja x
--      | Nodo x i d => Nodo x (espejo d) (espejo i)
-- y la que aplana el árbol es
--    def aplana : Arbol α → List α
--      | Hoja x     => [x]
--      | Nodo x i d => (aplana i) ++ [x] ++ (aplana d)
--
-- Demostrar que
--    aplana (espejo a) = reverse (aplana a)
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- De las definiciones de las funciones espejo y aplana se obtienen los
-- siguientes lemas
--    espejo1 : espejo (Hoja x) = Hoja x
--    espejo2 : espejo (Nodo x i d) = Nodo x (espejo d) (espejo i)
--    aplana1 : aplana (Hoja x) = [x]
--    aplana2 : aplana (Nodo x i d) = (aplana i) ++ [x] ++ (aplana d)
--
-- Demostraremos que, para todo árbol a,
--    aplana (espejo a) = reverse (aplana a)
-- por inducción sobre a.
--
-- Caso base: Supongamos que a = Hoja x. Entonces,
--    aplana (espejo a)
--    = aplana (espejo (Hoja x))
--    = aplana (Hoja x)              [por espejo1]
--    = [x]                          [por aplana1]
--    = reverse [x]
--    = reverse (aplana (Hoja x))    [por aplana1]
--    = reverse (aplana a)
--
-- Paso de inducción: Supongamos que a = Nodo x i d y se cumplen las
-- hipótesis de inducción
--    aplana (espejo i) = reverse (aplana i)                        (Hi)
--    aplana (espejo d) = reverse (aplana d)                        (Hd)
-- Entonces,
--    aplana (espejo a)
--    = aplana (espejo (Nodo x i d))
--    = aplana (Nodo x (espejo d) (espejo i))                     [por espejo2]
--    = (aplana (espejo d) ++ [x]) ++ aplana (espejo i)           [por aplana2]
--    = (reverse (aplana d) ++ [x]) ++ aplana (espejo i)          [por Hd]
--    = (reverse (aplana d) ++ [x]) ++ reverse (aplana i)         [por Hi]
--    = (reverse (aplana d) ++ reverse [x]) ++ reverse (aplana i)
--    = reverse ([x] ++ aplana d) ++ reverse (aplana i)
--    = reverse (aplana i ++ ([x] ++ aplana d))
--    = reverse ((aplana i ++ [x]) ++ aplana d)
--    = reverse (aplana (Nodo x i d))                             [por aplana2]
--    = reverse (aplana a)

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

open List

variable {α : Type}

-- Para que no use la notación con puntos
set_option pp.fieldNotation false

inductive Arbol (α : Type) : Type
  | Hoja : α → Arbol α
  | Nodo : α → Arbol α → Arbol α → Arbol α

namespace Arbol

variable (a i d : Arbol α)
variable (x : α)

def espejo : Arbol α → Arbol α
  | Hoja x     => Hoja x
  | Nodo x i d => Nodo x (espejo d) (espejo i)

@[simp]
lemma espejo_1 :
  espejo (Hoja x) = Hoja x := rfl

@[simp]
lemma espejo_2 :
  espejo (Nodo x i d) = Nodo x (espejo d) (espejo i) := rfl

def aplana : Arbol α → List α
  | Hoja x     => [x]
  | Nodo x i d => (aplana i) ++ [x] ++ (aplana d)

@[simp]
lemma aplana_1 :
  aplana (Hoja x) = [x] := rfl

@[simp]
lemma aplana_2 :
  aplana (Nodo x i d) = (aplana i) ++ [x] ++ (aplana d) := rfl

-- 1ª demostración
-- ===============

example :
  aplana (espejo a) = reverse (aplana a) :=
by
  induction a with
  | Hoja x =>
    -- x : α
    -- ⊢ aplana (espejo (Hoja x)) = reverse (aplana (Hoja x))
    rw [espejo_1]
    -- ⊢ aplana (Hoja x) = reverse (aplana (Hoja x))
    rw [aplana_1]
    -- ⊢ [x] = reverse [x]
    rw [reverse_singleton]
  | Nodo x i d Hi Hd =>
    -- x : α
    -- i d : Arbol α
    -- Hi : aplana (espejo i) = reverse (aplana i)
    -- Hd : aplana (espejo d) = reverse (aplana d)
    -- ⊢ aplana (espejo (Nodo x i d)) = reverse (aplana (Nodo x i d))
    rw [espejo_2]
    -- ⊢ aplana (Nodo x (espejo d) (espejo i)) = reverse (aplana (Nodo x i d))
    rw [aplana_2]
    -- ⊢ aplana (espejo d) ++ [x] ++ aplana (espejo i) = reverse (aplana (Nodo x i d))
    rw [Hi, Hd]
    -- ⊢ reverse (aplana d) ++ [x] ++ reverse (aplana i) = reverse (aplana (Nodo x i d))
    rw [aplana_2]
    -- ⊢ reverse (aplana d) ++ [x] ++ reverse (aplana i) = reverse (aplana i ++ [x] ++ aplana d)
    rw [reverse_append]
    -- ⊢ reverse (aplana d) ++ [x] ++ reverse (aplana i) = reverse (aplana d) ++ reverse (aplana i ++ [x])
    rw [reverse_append]
    -- ⊢ reverse (aplana d) ++ [x] ++ reverse (aplana i) = reverse (aplana d) ++ (reverse [x] ++ reverse (aplana i))
    rw [reverse_singleton]
    -- ⊢ reverse (aplana d) ++ [x] ++ reverse (aplana i) = reverse (aplana d) ++ ([x] ++ reverse (aplana i))
    rw [append_assoc]

-- 2ª demostración
-- ===============

example :
  aplana (espejo a) = reverse (aplana a) :=
by
  induction a with
  | Hoja x =>
    calc aplana (espejo (Hoja x))
         = aplana (Hoja x)
             := congr_arg aplana (espejo_1 x)
       _ = [x]
             := aplana_1 x
       _ = reverse [x]
             := reverse_singleton x
       _ = reverse (aplana (Hoja x))
             := congr_arg reverse (aplana_1 x).symm
  | Nodo x i d Hi Hd =>
    calc aplana (espejo (Nodo x i d))
         = aplana (Nodo x (espejo d) (espejo i))
             := congr_arg aplana (espejo_2 i d x)
       _ = (aplana (espejo d) ++ [x]) ++ aplana (espejo i)
             := aplana_2 (espejo d) (espejo i) x
       _ = (reverse (aplana d) ++ [x]) ++ aplana (espejo i)
             := congrArg (fun y => (y ++ [x]) ++ aplana (espejo i)) Hd
       _ = (reverse (aplana d) ++ [x]) ++ reverse (aplana i)
             := congrArg ((reverse (aplana d) ++ [x]) ++ .) Hi
       _ = (reverse (aplana d) ++ reverse [x]) ++ reverse (aplana i)
             := congrArg (fun y => (reverse (aplana d) ++ y) ++ reverse (aplana i))
                         (reverse_singleton x).symm
       _ = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             := congrArg (. ++ reverse (aplana i)) (reverse_append [x] (aplana d)).symm
       _ = reverse (aplana i ++ ([x] ++ aplana d))
             := (reverse_append (aplana i) ([x] ++ aplana d)).symm
       _ = reverse ((aplana i ++ [x]) ++ aplana d)
             := congr_arg reverse (append_assoc (aplana i) [x] (aplana d)).symm
       _ = reverse (aplana (Nodo x i d))
             := congr_arg reverse (aplana_2 i d x)

-- 3ª demostración
-- ===============

example :
  aplana (espejo a) = reverse (aplana a) :=
by
  induction a with
  | Hoja x =>
    -- x : α
    -- ⊢ aplana (espejo (Hoja x)) = reverse (aplana (Hoja x))
    calc aplana (espejo (Hoja x))
         = aplana (Hoja x)
             := by simp only [espejo_1]
       _ = [x]
             := by rw [aplana_1]
       _ = reverse [x]
             := by rw [reverse_singleton]
       _ = reverse (aplana (Hoja x))
             := by simp only [aplana_1]
  | Nodo x i d Hi Hd =>
    -- x : α
    -- i d : Arbol α
    -- Hi : aplana (espejo i) = reverse (aplana i)
    -- Hd : aplana (espejo d) = reverse (aplana d)
    -- ⊢ aplana (espejo (Nodo x i d)) = reverse (aplana (Nodo x i d))
    calc aplana (espejo (Nodo x i d))
         = aplana (Nodo x (espejo d) (espejo i))
             := by simp only [espejo_2]
       _ = aplana (espejo d) ++ [x] ++ aplana (espejo i)
             := by rw [aplana_2]
       _ = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             := by rw [Hi, Hd]
       _ = reverse (aplana d) ++ reverse [x] ++ reverse (aplana i)
             := by simp only [reverse_singleton]
       _ = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             := by simp only [reverse_append]
       _ = reverse (aplana i ++ ([x] ++ aplana d))
             := by simp only [reverse_append]
       _ = reverse (aplana i ++ [x] ++ aplana d)
             := by simp only [append_assoc]
       _ = reverse (aplana (Nodo x i d))
             := by simp only [aplana_2]

-- 3ª demostración
-- ===============

example :
  aplana (espejo a) = reverse (aplana a) :=
by
  induction a with
  | Hoja x =>
    calc aplana (espejo (Hoja x))
         = aplana (Hoja x)           := by simp
       _ = [x]                       := by simp
       _ = reverse [x]               := by simp
       _ = reverse (aplana (Hoja x)) := by simp
  | Nodo x i d Hi Hd =>
    calc aplana (espejo (Nodo x i d))
         = aplana (Nodo x (espejo d) (espejo i))
             := by simp
       _ = aplana (espejo d) ++ [x] ++ aplana (espejo i)
             := by simp
       _ = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             := by simp [Hi, Hd]
       _ = reverse (aplana d) ++ reverse [x] ++ reverse (aplana i)
             := by simp
       _ = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             := by simp
       _ = reverse (aplana i ++ ([x] ++ aplana d))
             := by simp
       _ = reverse (aplana i ++ [x] ++ aplana d)
             := by simp
       _ = reverse (aplana (Nodo x i d))
             := by simp

-- 5ª demostración
-- ===============

example :
  aplana (espejo a) = reverse (aplana a) :=
by
  induction a with
  | Hoja x =>
    simp
  | Nodo x i d Hi Hd =>
     calc aplana (espejo (Nodo x i d))
         = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             := by simp [Hi, Hd]
       _ = reverse (aplana (Nodo x i d))
             := by simp

-- 6ª demostración
-- ===============

example :
  aplana (espejo a) = reverse (aplana a) :=
by
  induction a with
  | Hoja _ => simp
  | Nodo _ _ _ Hi Hd => simp [Hi, Hd]

-- 7ª demostración
-- ===============

example :
  aplana (espejo a) = reverse (aplana a) :=
by induction a <;> simp [*]

-- 8ª demostración
-- ===============

lemma aplana_espejo :
  ∀ a : Arbol α, aplana (espejo a) = reverse (aplana a)
  | Hoja x     => by simp
  | Nodo x i d => by simp [aplana_espejo i,
                           aplana_espejo d]

end Arbol

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (xs ys zs : List α)
-- #check (append_assoc xs ys zs : (xs ++ ys) ++ zs = xs ++ (ys ++ zs))
-- #check (reverse_append xs ys : reverse (xs ++ ys) = reverse ys ++ reverse xs)
-- #check (reverse_singleton x : reverse [x] = [x])

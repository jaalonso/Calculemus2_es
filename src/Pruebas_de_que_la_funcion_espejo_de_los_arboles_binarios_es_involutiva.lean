-- Pruebas_de_que_la_funcion_espejo_de_los_arboles_binarios_es_involutiva.lean
-- Pruebas de que la función espejo de los árboles binarios es involutiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-agosto-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- El árbol correspondiente a
--        3
--       / \
--      2   4
--     / \
--    1   5
-- se puede representar por el término
--    nodo 3 (nodo 2 (hoja 1) (hoja 5)) (hoja 4)
-- usado el tipo de dato arbol definido por
--    inductive arbol (α : Type) : Type
--    | hoja : α → arbol
--    | nodo : α → arbol → arbol → arbol
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
--    def espejo : arbol α → arbol α
--    | (hoja x)     := hoja x
--    | (nodo x i d) := nodo x (espejo d) (espejo i)
--
-- Demostrar que la función espejo es involutiva; es decir,
--    espejo (espejo a) = a
-- ---------------------------------------------------------------------

import Mathlib.Tactic

variable {α : Type}

-- Para que no use la notación con puntos
set_option pp.fieldNotation false

inductive Arbol (α : Type) : Type
  | hoja : α → Arbol α
  | nodo : α → Arbol α → Arbol α → Arbol α
  deriving DecidableEq, Repr

namespace Arbol

def ej_Arbol : Arbol Nat :=
  nodo 3 (hoja 4) (nodo 2 (hoja 5) (hoja 1))

-- #eval ej_Arbol

variable (a i d : Arbol α)
variable (x : α)

def espejo : Arbol α → Arbol α
  | (hoja x)     => hoja x
  | (nodo x i d) => nodo x (espejo d) (espejo i)

@[simp]
lemma espejo_1 :
  espejo (hoja x) = hoja x := rfl

@[simp]
lemma espejo_2 :
  espejo (nodo x i d) = nodo x (espejo d) (espejo i) := rfl

-- 1ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by
  induction' a with x x i d Hi Hd
  . -- x : α
    -- ⊢ espejo (espejo (hoja x)) = hoja x
    rw [espejo_1]
    -- ⊢ espejo (hoja x) = hoja x
    rw [espejo_1]
  . -- x : α
    -- i d : Arbol α
    -- Hi : espejo (espejo i) = i
    -- Hd : espejo (espejo d) = d
    -- ⊢ espejo (espejo (nodo x i d)) = nodo x i d
    rw [espejo_2]
    -- ⊢ espejo (nodo x (espejo d) (espejo i)) = nodo x i d
    rw [espejo_2]
    -- ⊢ nodo x (espejo (espejo i)) (espejo (espejo d)) = nodo x i d
    rw [Hi]
    -- ⊢ nodo x i (espejo (espejo d)) = nodo x i d
    rw [Hd]

-- 2ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by
  induction' a with x x i d Hi Hd
  . -- x : α
    -- ⊢ espejo (espejo (hoja x)) = hoja x
    calc espejo (espejo (hoja x))
         = espejo (hoja x) := congr_arg espejo (espejo_1 x)
       _ = hoja x          := espejo_1 x
  . -- x : α
    -- i d : Arbol α
    -- Hi : espejo (espejo i) = i
    -- Hd : espejo (espejo d) = d
    -- ⊢ espejo (espejo (nodo x i d)) = nodo x i d
    calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             := congr_arg espejo (espejo_2 i d x)
       _ = nodo x (espejo (espejo i)) (espejo (espejo d))
             := espejo_2 (espejo d) (espejo i) x
       _ = nodo x i (espejo (espejo d))
             := congrArg (nodo x . (espejo (espejo d))) Hi
       _ = nodo x i d
             := congrArg (nodo x i .) Hd

-- 3ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by
  induction' a with x x i d Hi Hd
  . -- ⊢ espejo (espejo (hoja x)) = hoja x
    calc espejo (espejo (hoja x))
         = espejo (hoja x) := congr_arg espejo (espejo_1 x)
       _ = hoja x          := by rw [espejo_1]
  . -- x : α
    -- i d : Arbol α
    -- Hi : espejo (espejo i) = i
    -- Hd : espejo (espejo d) = d
    -- ⊢ espejo (espejo (nodo x i d)) = nodo x i d
    calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             := congr_arg espejo (espejo_2 i d x)
       _ = nodo x (espejo (espejo i)) (espejo (espejo d))
             := by rw [espejo_2]
       _ = nodo x i (espejo (espejo d))
             := by rw [Hi]
       _ = nodo x i d
             := by rw [Hd]

-- 4ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by
  induction' a with x x i d Hi Hd
  . -- x : α
    -- ⊢ espejo (espejo (hoja x)) = hoja x
    calc espejo (espejo (hoja x))
         = espejo (hoja x) := by simp
       _ = hoja x          := by simp
  . -- x : α
    -- i d : Arbol α
    -- Hi : espejo (espejo i) = i
    -- Hd : espejo (espejo d) = d
    -- ⊢ espejo (espejo (nodo x i d)) = nodo x i d
    calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             := by simp
       _ = nodo x (espejo (espejo i)) (espejo (espejo d))
             := by simp
       _ = nodo x i (espejo (espejo d))
             := by simp [Hi]
       _ = nodo x i d
             := by simp [Hd]

-- 5ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by
  induction' a with _ _ _ _ Hi Hd
  . simp
  . simp [Hi, Hd]

-- 6ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by induction' a <;> simp [*]

-- 7ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by induction a with
  | hoja x =>
    -- ⊢ espejo (espejo (hoja x)) = hoja x
    calc espejo (espejo (hoja x))
         = espejo (hoja x) := congr_arg espejo (espejo_1 x)
       _ = hoja x          := espejo_1 x
  | nodo x i d Hi Hd =>
    -- x : α
    -- i d : Arbol α
    -- Hi : espejo (espejo i) = i
    -- Hd : espejo (espejo d) = d
    -- ⊢ espejo (espejo (nodo x i d)) = nodo x i d
    calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             := congr_arg espejo (espejo_2 i d x)
       _ = nodo x (espejo (espejo i)) (espejo (espejo d))
             := espejo_2 (espejo d) (espejo i) x
       _ = nodo x i (espejo (espejo d))
             := congrArg (nodo x . (espejo (espejo d))) Hi
       _ = nodo x i d
             := congrArg (nodo x i .) Hd

-- 8ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by induction a with
  | hoja x =>
    -- ⊢ espejo (espejo (hoja x)) = hoja x
    simp
  | nodo x i d Hi Hd =>
    -- x : α
    -- i d : Arbol α
    -- Hi : espejo (espejo i) = i
    -- Hd : espejo (espejo d) = d
    -- ⊢ espejo (espejo (nodo x i d)) = nodo x i d
    simp [Hi, Hd]

-- 9ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by induction a <;> simp [*]

-- 10ª demostración
-- ===============

lemma espejo_espejo :
  ∀ a : Arbol α, espejo (espejo a) = a
  | (hoja x)     => by simp
  | (nodo x i d) => by simp [espejo_espejo i, espejo_espejo d]

end Arbol

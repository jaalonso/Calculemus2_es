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
-- usando el tipo de dato arbol definido por
--    inductive Arbol (α : Type) : Type
--      | hoja : α → Arbol α
--      | nodo : α → Arbol α → Arbol α → Arbol α
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

-- Demostración en lenguaje natural
-- ================================

-- De la definición de la función espejo se obtienen los siguientes
-- lemas
--    espejo1 : espejo (hoja x) = hoja x
--    espejo2 : espejo (nodo x i d) = nodo x (espejo d) (espejo i)
--
-- Demostraremos que, para todo árbol a,
--    espejo (espejo a) = a
-- por inducción sobre a.
--
-- Caso base: Supongamos que a = hoja x. Entonces,
--    espejo (espejo a)
--    = espejo (espejo (hoja x))
--    = espejo (hoja x)             [por espejo1]
--    = hoja x                      [por espejo1]
--    = a
--
-- Paso de inducción: Supongamos que a = nodo x i d y se cumplen las
-- hipótesis de inducción
--    espejo (espejo i) = i                                         (Hi)
--    espejo (espejo d) = d                                         (Hi)
-- Entonces,
--    espejo (espejo a)
--    = espejo (espejo (nodo x i d))
--    = espejo (nodo x (espejo d) (espejo i))             [por espejo2]
--    = nodo x (espejo (espejo i)) (espejo (espejo d))    [por espejo2]
--    = nodo x i (espejo (espejo d))                      [por Hi]
--    = nodo x i d                                        [por Hd]
--    = a

-- Demostraciones con Lean4
-- ========================

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
  induction a with
  | hoja x =>
    -- x : α
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

-- 2ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by
  induction a with
  | hoja x =>
    -- ⊢ espejo (espejo (hoja x)) = hoja x
    calc espejo (espejo (hoja x))
         = espejo (hoja x) := congr_arg espejo (espejo_1 x)
       _ = hoja x          := by rw [espejo_1]
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
             := by rw [espejo_2]
       _ = nodo x i (espejo (espejo d))
             := by rw [Hi]
       _ = nodo x i d
             := by rw [Hd]

-- 3ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by
  induction a with
  | hoja x =>
    -- x : α
    -- ⊢ espejo (espejo (hoja x)) = hoja x
    calc espejo (espejo (hoja x))
         = espejo (hoja x) := by simp
       _ = hoja x          := by simp
  | nodo x i d Hi Hd =>
     -- x : α
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

-- 4ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by
  induction a with
  | hoja _ => simp
  | nodo _ _ _ Hi Hd => simp [Hi, Hd]

-- 5ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by induction a <;> simp [*]

-- 6ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by
  induction a with
  | hoja x =>
    -- x : α
    -- ⊢ espejo (espejo (hoja x)) = hoja x
    rw [espejo_1]
    -- ⊢ espejo (hoja x) = hoja x
    rw [espejo_1]
  | nodo x i d Hi Hd =>
    -- x : α
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

-- 7ª demostración
-- ===============

example :
  espejo (espejo a) = a :=
by
  induction a with
  | hoja x =>
    -- x : α
    -- ⊢ espejo (espejo (hoja x)) = hoja x
    rw [espejo_1, espejo_1]
  | nodo x i d Hi Hd =>
    -- x : α
    -- i d : Arbol α
    -- Hi : espejo (espejo i) = i
    -- Hd : espejo (espejo d) = d
    -- ⊢ espejo (espejo (nodo x i d)) = nodo x i d
    rw [espejo_2, espejo_2, Hi, Hd]

-- 8ª demostración
-- ===============

lemma espejo_espejo :
  ∀ a : Arbol α, espejo (espejo a) = a
  | (hoja x)     => by simp
  | (nodo x i d) => by simp [espejo_espejo i, espejo_espejo d]

end Arbol

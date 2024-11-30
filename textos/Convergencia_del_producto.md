---
title: El límite del producto de dos sucesiones convergentes es el producto de sus límites
date: 2024-11-30 06:00:00 UTC+02:00
category: Limite
has_math: true
---

En Lean, una sucesión \\(u_0, u_1, u_2, ...\\) se puede representar mediante una función \\(u : ℕ → ℝ\\) de forma que \\(u(n)\\) es \\(u_n\\).

Se define que \\(a\\) límite de la sucesión \\(u\\), por
~~~lean
   def limite (u : ℕ → ℝ) (c : ℝ) :=
     ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε
~~~

Demostrar que si \\(u_n\\) converge a \\(a\\) y \\(v_n\\) a \\(b\\), entonces \\(u_nv_n\\) converge a \\(ab\\).

Para ello, completar la siguiente teoría de Lean4:

~~~lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u v : ℕ → ℝ}
variable {a b : ℝ}

def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (fun n ↦ u n * v n) (a * b) :=
by sorry
~~~
<!-- TEASER_END -->

# 1. Demostración en lenguaje natural

La demostración se basará en los siguientes lemas demostrados en
ejercicios anteriores:

+ Lema 1. Son equivalentes \\(\\lim\\limits_{n \\to \\infty} u_n = a\\) y \\(\\lim\\limits_{n \\to \\infty} (u_n-a) = 0\\).
+ Lema 2. Si \\(\\lim\\limits_{n \\to \\infty} u_n = 0\\) y \\(\\lim\\limits_{n \\to \\infty} v_n = 0\\), entonces \\(\\lim\\limits_{n \\to \\infty} u_nv_n = 0\\).
+ Lema 3. Si \\(\\lim\\limits_{n \\to \\infty} u_n = a\\) y \\(c ∈ ℝ\\), entonces \\(\\lim\\limits_{n \\to \\infty} cu_n = ca\\).
+ Lema 4. Si \\(\\lim\\limits_{n \\to \\infty} u_n = a\\) y \\(c ∈ ℝ\\), entonces \\(\\lim\\limits_{n \\to \\infty} u_nc = ac\\).
+ Lema 5. Si \\(\\lim\\limits_{n \\to \\infty} u_n = a\\) y \\(\\lim\\limits_{n \\to \\infty} v_n = b\\), entonces \\(\\lim\\limits_{n \\to \\infty} (u_n+v_n) = a+b\\).

Por el lema 1, puesto que \\(\\lim\\limits_{n \\to \\infty} u_n = a\\) y \\(\\lim\\limits_{n \\to \\infty} v_n b\\), se tiene que
\\[ \\lim\\limits_{n \\to \\infty} (u_n - a) = 0 \\tag{1} \\]
\\[ \\lim\\limits_{n \\to \\infty} (v_n - b) = 0 \\tag{2} \\]
Por el lema 2, (1) y (2) se tiene que
\\[ \\lim\\limits_{n \\to \\infty} (u_n - a)(v_n - b) = 0 \\tag{3} \\]
Por el lema 3 y (2) se tiene que
\\[ \\lim\\limits_{n \\to \\infty} a(v_n - b) = a·0 \\tag{4} \\]
Por el lema 4 y (1) se tiene que
\\[ \\lim\\limits_{n \\to \\infty} (u_n - a)b = 0·b \\tag{5} \\]
Por el lema 5, (3), (4) y (5) se tiene que
\\[ \\lim\\limits_{n \\to \\infty} ((u_n-a)(v_n-b)+a·(v_n-b)+(u_n-a)·b) = 0+t·0+0·u \\]
y, simplificando, queda
\\[ \\lim\\limits_{n \\to \\infty} (u_nv_n - ab) = 0 \tag{6} \\]
Finalmente, por el lema 1 y (6), se tiene que
\\[ \\lim\\limits_{n \\to \\infty} u_nv_n = ab\\]

# 2. Demostraciones con Lean4

~~~lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u v : ℕ → ℝ}
variable {a b : ℝ}

def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε

-- Lema 1. El límite de uₙ es a syss el de uₙ-a es 0
-- (ver demostraciones en https://tinyurl.com/22nkht98)
lemma CNS_limite :
  limite u a ↔ limite (fun i ↦ u i - a) 0 :=
by
  rw [iff_eq_eq]
  calc limite u a
       = ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε       := rfl
     _ = ∀ ε > 0, ∃ N, ∀ n ≥ N, |(u n - a) - 0| < ε := by simp
     _ = limite (fun i ↦ u i - a) 0                 := rfl

-- Lema 2. Si uₙ y vₙ convergen a cero, entonces uₙvₙ converge a 0
-- (ver demostraciones en https://tinyurl.com/2ag9plvs )
lemma prod_convergen_a_cero
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  obtain ⟨U, hU⟩ := hu ε hε
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - 0| < ε
  obtain ⟨V, hV⟩ := hv 1 zero_lt_one
  -- V : ℕ
  -- hV : ∀ (n : ℕ), n ≥ V → |v n - 0| < 1
  let N := max U V
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(u * v) n - 0| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |(u * v) n - 0| < ε
  specialize hU n (le_of_max_le_left hn)
  -- hU : |u n - 0| < ε
  specialize hV n (le_of_max_le_right hn)
  -- hV : |v n - 0| < 1
  rw [sub_zero] at *
  -- hU : |u n - 0| < ε
  -- hV : |v n - 0| < 1
  -- ⊢ |(u * v) n - 0| < ε
  calc |(u * v) n|
       = |u n * v n|
         := rfl
     _ = |u n| * |v n|
         := abs_mul (u n) (v n)
     _ < ε * 1
         := mul_lt_mul'' hU hV (abs_nonneg (u n)) (abs_nonneg (v n))
     _ = ε
         := mul_one ε

-- Lema 3. Si el límite de la sucesión uₙ es a y c ∈ ℝ, entonces el
-- límite de cuₙ es ca (ver demostraciones en https://tinyurl.com/2244qcxs )
lemma limite_por_const
  (h : limite u a)
  : limite (fun n ↦ c * (u n)) (c * a) :=
by
  by_cases hc : c = 0
  . -- hc : c = 0
    subst hc
    -- ⊢ limite (fun n => 0 * u n) (0 * a)
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => 0 * u n) n - 0 * a| < ε
    aesop
  . -- hc : ¬c = 0
    intros ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    have hc' : 0 < |c| := abs_pos.mpr hc
    have hεc : 0 < ε / |c| := div_pos hε hc'
    specialize h (ε/|c|) hεc
    -- h : ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    obtain ⟨N, hN⟩ := h
    -- N : ℕ
    -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / |c|
    use N
    -- ⊢ ∀ (n : ℕ), n ≥ N → |(fun n => c * u n) n - c * a| < ε
    intros n hn
    -- n : ℕ
    -- hn : n ≥ N
    -- ⊢ |(fun n => c * u n) n - c * a| < ε
    specialize hN n hn
    -- hN : |u n - a| < ε / |c|
    dsimp only
    calc |c * u n - c * a|
         = |c * (u n - a)| := congr_arg abs (mul_sub c (u n) a).symm
       _ = |c| * |u n - a| := abs_mul c  (u n - a)
       _ < |c| * (ε / |c|) := (mul_lt_mul_left hc').mpr hN
       _ = ε               := mul_div_cancel₀ ε (ne_of_gt hc')

-- Lema 4. Si el límite de la sucesión uₙ es a y c ∈ ℝ, entonces el
-- límite de uₙc es ac (ver demostraciones en https://tinyurl.com/2xr94fh4 )
lemma const_por_limite
  (h : limite u a)
  : limite (fun n ↦ (u n) * c) (a * c) :=
by
  have h1 : ∀ n, (u n) * c = c * (u n) := by
    intro
    -- n : ℕ
    -- ⊢ u n * c = c * u n
    ring
  have h2 : a * c = c * a := mul_comm a c
  simp [h1,h2]
  -- ⊢ limite (fun n => c * u n) (c * a)
  exact limite_por_const h

-- Lema 5. Si la sucesión uₙ converge a a y la vₙ a b, entonces uₙ+vₙ
-- converge a a+b (ver demostraciones en https://tinyurl.com/294wn94r )
lemma limite_suma
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(u + v) n - (a + b)| < ε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨Nu, hNu⟩ := hu (ε / 2) hε2
  -- Nu : ℕ
  -- hNu : ∀ (n : ℕ), n ≥ Nu → |u n - a| < ε / 2
  obtain ⟨Nv, hNv⟩ := hv (ε / 2) hε2
  -- Nv : ℕ
  -- hNv : ∀ (n : ℕ), n ≥ Nv → |v n - b| < ε / 2
  clear hu hv hε2 hε
  let N := max Nu Nv
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(s + t) n - (a + b)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  have nNu : n ≥ Nu := le_of_max_le_left hn
  specialize hNu n nNu
  -- hNu : |u n - a| < ε / 2
  have nNv : n ≥ Nv := le_of_max_le_right hn
  specialize hNv n nNv
  -- hNv : |v n - b| < ε / 2
  clear hn nNu nNv
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)|  := rfl
     _ = |(u n - a) + (v n - b)|  := by { congr; ring }
     _ ≤ |u n - a| + |v n - b|    := by apply abs_add
     _ < ε / 2 + ε / 2            := by linarith [hNu, hNv]
     _ = ε                        := by apply add_halves

-- 1ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (fun n ↦ u n * v n) (a * b) :=
by
  rw [CNS_limite] at *
  -- hu : limite (fun i => u i - a) 0
  -- hv : limite (fun i => v i - b) 0
  -- ⊢ limite (fun i => u i * v i - a * b) 0
  have h : ∀ n, u n * v n - a * b
                = (u n - a) * (v n - b)
                  + a * (v n - b)
                  + (u n - a) * b := by
    intro n
    -- n : ℕ
    -- ⊢ u n * v n - a * b
    --   = (u n - a) * (v n - b) + a * (v n - b) + (u n - a) * b
    ring
  simp [h]
  -- ⊢ limite (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   0
  rw [show (0 : ℝ) = 0 + a * 0 + 0 * b by simp]
  -- ⊢ limite (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   (0 + a * 0 + 0 * b)
  have h1 : limite (fun n => (u n - a) * (v n - b)) 0
    := prod_convergen_a_cero hu hv
  have h2 : limite (fun n => a * (v n - b)) (a * 0)
    := limite_por_const hv
  have h3 : limite (fun n => (u n - a) * b) (0 * b)
    := const_por_limite hu
  exact limite_suma (limite_suma h1 h2) h3

-- 2ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (fun n ↦ u n * v n) (a * b) :=
by
  rw [CNS_limite] at *
  -- hu : limite (fun i => u i - a) 0
  -- hv : limite (fun i => v i - b) 0
  -- ⊢ limite (fun i => u i * v i - a * b) 0
  have h : ∀ n, u n * v n - a * b
                = (u n - a) * (v n - b)
                  + a * (v n - b)
                  + (u n - a) * b := by
    intro n
    -- n : ℕ
    -- ⊢ u n * v n - a * b
    --   = (u n - a) * (v n - b) + a * (v n - b) + (u n - a) * b
    ring
  simp [h]
  -- ⊢ limite (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   0
  rw [show (0 : ℝ) = 0 + a * 0 + 0 * b by simp]
  -- ⊢ limite (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   (0 + a * 0 + 0 * b)
  apply limite_suma
  . -- ⊢ limite (fun i => (u i - a) * (v i - b) + a * (v i - b)) (0 + a * 0)
    apply limite_suma
    . -- ⊢ limite (fun i => (u i - a) * (v i - b)) 0
      exact prod_convergen_a_cero hu hv
    . -- ⊢ limite (fun i => a * (v i - b)) (a * 0)
      exact limite_por_const hv
  . -- ⊢ limite (fun i => (u i - a) * b) (0 * b)
    exact const_por_limite hu

-- 3ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (fun n ↦ u n * v n) (a * b) :=
by
  rw [CNS_limite] at *
  -- hu : limite (fun i => u i - a) 0
  -- hv : limite (fun i => v i - b) 0
  -- ⊢ limite (fun i => u i * v i - a * b) 0
  have h : ∀ n, u n * v n - a * b
                = (u n - a) * (v n - b)
                  + a * (v n - b)
                  + (u n - a) * b := by
    intro n
    -- n : ℕ
    -- ⊢ u n * v n - a * b
    --   = (u n - a) * (v n - b) + a * (v n - b) + (u n - a) * b
    ring
  simp [h]
  -- ⊢ limite (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   0
  rw [show (0 : ℝ) = 0 + a * 0 + 0 * b by simp]
  -- ⊢ limite (fun i => (u i - a) * (v i - b) + a * (v i - b) + (u i - a) * b)
  --   (0 + a * 0 + 0 * b)
  refine' limite_suma (limite_suma _ _) _
  · -- ⊢ limite (fun i => (u i - a) * (v i - b)) 0
    exact prod_convergen_a_cero hu hv
  · -- ⊢ limite (fun i => a * (v i - b)) (a * 0)
    exact limite_por_const hv
  · -- ⊢ limite (fun i => (u i - a) * b) (0 * b)
    exact const_por_limite hu

-- Lemas usados
-- ============

-- variable (p q : Prop)
-- variable (c d x y: ℝ)
-- variable (f : ℝ → ℝ)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (abs_nonneg a : 0 ≤ |a|)
-- #check (abs_pos.mpr : a ≠ 0 → 0 < |a|)
-- #check (add_halves a : a / 2 + a / 2 = a)
-- #check (congr_arg f : x = y → f x = f y)
-- #check (div_pos : 0 < a → 0 < b → 0 < a / b)
-- #check (iff_eq_eq : (p ↔ q) = (p = q))
-- #check (le_of_max_le_left : max a b ≤ c → a ≤ c)
-- #check (le_of_max_le_right : max a b ≤ c → b ≤ c)
-- #check (mul_comm a b : a * b = b * a)
-- #check (mul_div_cancel₀ a : b ≠ 0 → b * (a / b) = a)
-- #check (mul_lt_mul'' : a < c → b < d → 0 ≤ a → 0 ≤ b → a * b < c * d)
-- #check (mul_lt_mul_left : 0 < a → (a * b < a * c ↔ b < c))
-- #check (mul_one a : a * 1 = a)
-- #check (mul_sub a b c : a * (b - c) = a * b - a * c)
-- #check (ne_of_gt : b < a → a ≠ b)
-- #check (zero_lt_one : 0 < 1)
~~~

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Convergencia_de_producto.lean).

# Referencias

+ Kevin Buzzard. [Formalising Mathematics (2024), Section02reals, Sheet6.lean](https://github.com/ImperialCollegeLondon/formalising-mathematics-2024/blob/b732ed1352e87b4474b0520d1383994e069f8057/FormalisingMathematics2024/Solutions/Section02reals/Sheet6.lean#L116-L131).

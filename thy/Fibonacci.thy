(* Fibonacci.thy
-- Pruebas de equivalencia de definiciones de la función de Fibonacci.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-agosto-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, se puede definir la función de Fibonacci por
--   fun fibonacci :: "nat \<Rightarrow> nat" 
--     where
--       "fibonacci 0 = 0" 
--     | "fibonacci (Suc 0) = 1" 
--     | "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"
--
-- Otra definición es
--    fun fibAux :: "nat => nat \<times> nat" 
--     where
--        "fibAux 0 = (0, 1)" 
--     | "fibAux (Suc n) = (let (a, b) = fibAux n in (b, a + b))"
--
--   definition fib :: "nat \<Rightarrow> nat" where
--     "fib n = fst (fibAux n)"
--
-- Demostrar que ambas definiciones son equivalentes; es decir,
--    fibonacci n = fib n
-- ------------------------------------------------------------------ *)

theory Fibonacci
imports Main
begin

fun fibonacci :: "nat \<Rightarrow> nat" 
  where
    "fibonacci 0 = 0" 
  | "fibonacci (Suc 0) = 1" 
  | "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"

fun fibAux :: "nat => nat \<times> nat" 
  where
     "fibAux 0 = (0, 1)" 
   | "fibAux (Suc n) = (let (a, b) = fibAux n in (b, a + b))"

definition fib :: "nat \<Rightarrow> nat" where
  "fib n = fst (fibAux n)"

lemma fib_suma : 
  "fib (Suc (Suc n)) = fib n + fib (Suc n)"
proof (induct n)
  show "fib (Suc (Suc 0)) = fib 0 + fib (Suc 0)"
    by (simp add: fib_def)
next
  fix n
  assume HI : "fib (Suc (Suc n)) = fib n + fib (Suc n)"
  have "fib (Suc (Suc (Suc n))) = fst (fibAux (Suc (Suc (Suc n))))"
    by (simp add: fib_def)
  also have "\<dots> = snd (fibAux (Suc (Suc n)))" 
    by (simp add: prod.case_eq_if)
  also have "\<dots> = fst (fibAux (Suc n)) + snd (fibAux (Suc n))"
    by (metis fibAux.simps(2) snd_conv split_def)
  also have "\<dots> = fib (Suc n) + snd (fibAux (Suc n))"
    using fib_def by auto
  also have "\<dots> = fib (Suc n) + fib (Suc (Suc n))"
    by (simp add: fib_def prod.case_eq_if)
  finally show "fib (Suc (Suc (Suc n))) = fib (Suc n) + fib (Suc (Suc n))"
    by this
qed

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
  also have "\<dots> = fib n + fib (Suc n)"
    by (simp add: HI1 HI2)
  also have "\<dots> = fib (Suc (Suc n))"
    by (simp add: fib_suma)
  finally show "fibonacci (Suc (Suc n)) = fib (Suc (Suc n))"
    by this
qed

end

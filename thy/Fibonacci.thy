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
--   fun fibAux :: "nat => nat \<times> nat" 
--     where
--        "fibAux 0 = (0, 1)" 
--     | "fibAux (Suc n) = (snd (fibAux n), fst (fibAux n) + snd (fibAux n))"
--
--   definition fib :: "nat \<Rightarrow> nat" where
--     "fib n = (fst (fibAux n))"
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
   | "fibAux (Suc n) = (snd (fibAux n), fst (fibAux n) + snd (fibAux n))"

definition fib :: "nat \<Rightarrow> nat" where
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
  also have "\<dots> = fib n + fib (Suc n)"
    by (simp add: HI1 HI2)
  also have "\<dots> = fib (Suc (Suc n))"
    by (simp add: fib_def)
  finally show "fibonacci (Suc (Suc n)) = fib (Suc (Suc n))"
    by this
qed

end

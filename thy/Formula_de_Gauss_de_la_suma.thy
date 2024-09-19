(* Formula_de_Gauss_de_la_suma.thy
-- Pruebas de "\<Sum>_{i<n} i = n(n-1)/2"
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 19-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- La fórmula de Gauss para la suma de los primeros números naturales es
--    0 + 1 + 2 + ... + (n-1) = n(n-1)/2
--
-- En un ejercicio anterior se ha demostrado dicha fórmula por
-- inducción. Otra forma de demostrarla, sin usar inducción, es la
-- siguiente: La suma se puede escribir de dos maneras
--    S = 0     + 1     + 2     + ... + (n-3) + (n-2) + (n-1)
--    S = (n-1) + (n-2) + (n-3) + ... + 2     + 1     + 0
-- Al sumar, se observa que cada par de números de la misma columna da
-- como suma (n-1), y puesto que hay n columnas en total, se sigue
--    2S = n(n-1)
-- lo que prueba la fórmula.
--
-- Demostrar la fórmula de Gauss siguiendo el procedimiento anterior.
-- ------------------------------------------------------------------ *)

theory Formula_de_Gauss_de_la_suma
imports Main
begin

lemma
  fixes n :: nat
  shows "2 * (\<Sum>i<n. i) = n * (n - 1)"
proof -
  have "2 * (\<Sum>i<n. i) = (\<Sum>i<n. i) + (\<Sum>i<n. i)"
    by simp
  also have "\<dots> = (\<Sum>i<n. i) + (\<Sum>i<n. n - Suc i)"
    using sum.nat_diff_reindex [where g = id] by auto
  also have "\<dots> = (\<Sum>i<n. (i + (n - Suc i)))"
    using sum.distrib [where A = "{..<n}" and
                             g = id and
                             h = "\<lambda>i. n - Suc i"] by auto
  also have "\<dots> = (\<Sum>i<n. n - 1)"
    by simp
  also have "\<dots> = n * (n -1)"
    using sum_constant by auto
  finally show "2 * (\<Sum>i<n. i) = n * (n - 1)" .
qed

end

-- SONDEO 2026-09-22 (c) — los CINCO de lista: ¿de verdad es «inducción sobre listas»?
--
-- El proyecto lleva escrito que `##`, `Π_p`, `ax_L2` y `ax_L3` quedan fuera del fragmento
-- porque «piden saber si un numeral es `nil` o `cons`, y eso es inducción sobre listas, que
-- `coreAxioms` no tiene». Eso es un ARGUMENTO, y en esta familia los argumentos han salido
-- mal cuatro veces (ADR-037). Este sondeo lo mide.
--
-- ⭐ La sospecha: el obstáculo NO es la ausencia de un esquema de inducción, sino que **la
-- codificación no es SOBREYECTIVA**. En Q⁺⁺:
--
--     nil      = 0
--     cons h t = pair h (σt) = π(h, t+1)        (π = emparejamiento de Cantor)
--
-- y `π(h,y)` con `y ≥ 1` **no cubre `ℕ`**: se deja fuera exactamente los `π(h,0)`, que son
-- los números triangulares. Con `consNat h t = T(h+t+1) + (t+1)`:
--
--     s=1 → 2 · s=2 → 4,5 · s=3 → 7,8,9 · s=4 → 11..14 · …
--
-- ⇒ los valores de `cons` son **todos menos {0, 1, 3, 6, 10, …}**. Y `0` es `nil`, así que
-- **1, 3, 6, 10, … no son NI `[]` NI `h::t`**.
--
-- 🔑 Si eso es así, «todo término es `[]` o un `::`» es **FALSO en el modelo estándar**, y
-- por tanto NO es que falte inducción para demostrarlo: es que **no hay nada que demostrar**.
-- Los cinco de lista estarían en la clase de `−` —INDETERMINADOS sobre la basura— y no en
-- la de `√` o `/₂`.
--
-- Uso: lake env lean sondeos/listas_probe.lean

import PeanoRF.HA.Fragment
open FOL PeanoRF.Calculus ROBINSON_PlusPlus.Minimal.Axioms
namespace PeanoRF.HA

set_option autoImplicit false

/-! ## La medición: `cons` nunca vale 1 -/

/-- Un `cons` codifica siempre **al menos 2**: el numerador es `s·(s+1) + 2y` con `s ≥ 1` e
    `y ≥ 1`, o sea ≥ 4, y la división entera por 2 conserva la cota. -/
theorem two_le_consNat (h t : Nat) : 2 ≤ consNat h t := by
  have hs : 1 ≤ h + (t + 1) := by omega
  have hmul : 1 * 2 ≤ (h + (t + 1)) * ((h + (t + 1)) + 1) :=
    Nat.mul_le_mul hs (by omega)
  have hnum : 4 ≤ (h + (t + 1)) * ((h + (t + 1)) + 1) + 2 * (t + 1) := by omega
  have hdiv : (4 : Nat) / 2 ≤ ((h + (t + 1)) * ((h + (t + 1)) + 1) + 2 * (t + 1)) / 2 :=
    Nat.div_le_div_right hnum
  simpa [consNat] using hdiv

/-- ⛔⛔ **`1` NO ES NI `[]` NI UN `::`.** Y lo mismo 3, 6, 10, … -/
theorem one_ne_consNat (h t : Nat) : consNat h t ≠ 1 := by
  have := two_le_consNat h t; omega

theorem one_ne_nil : (1 : Nat) ≠ 0 := by omega

/-- Los primeros valores, para que se vea el hueco: `cons` alcanza 2, 4, 5, 7, 8, 9, … y
    **se salta 1, 3, 6**. -/
example : consNat 0 0 = 2 := by decide
example : consNat 1 0 = 4 := by decide
example : consNat 0 1 = 5 := by decide
example : consNat 2 0 = 7 := by decide
example : consNat 1 1 = 8 := by decide
example : consNat 0 2 = 9 := by decide

/-! ## Lo que esto mide, y lo que NO

    ✅ **MEDIDO**: `cons` nunca vale 0 ni 1 — ni 3, ni 6, ni ningún triangular—, así que
    **la codificación de listas NO ES SOBREYECTIVA** y «todo término es `[]` o un `::`» es
    **falso en el modelo estándar**. ⇒ el obstáculo de los cinco de lista **no es** que
    falte un esquema de inducción para demostrarlo: es que **no hay nada que demostrar**.

    ⏳ **NO medido todavía**: que de ahí se siga que `∈`, `##` y `Π_p` quedan **libres**
    sobre esos códigos. Eso pide dos modelos que difieran ahí, y para tenerlos hace falta:

    * la **inyectividad del emparejamiento de Cantor** (`consNat h t = consNat h' t' →
      h = h' ∧ t = t'`), que es lo que hace bien definida la recursión de `∈`;
    * una relación `MemN` inductiva con `head`/`tail`, más una variante que además valga en
      `1` — las dos satisfacen `ax_L1` (porque `1 ≠ 0`) y `ax_L2` (porque `1` no es un
      `cons`), y difieren en `x ∈ 1̄`.

    🔑 Si eso sale, los cinco de lista caen en la clase de `−` —INDETERMINADOS, con
    medición negativa— y no en la de `√`. Sería la quinta vez que un ⛔ argumentado resulta
    ser de otra clase. -/

end PeanoRF.HA

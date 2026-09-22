-- SONDEO 2026-09-22 (b) — `numeralI_sqrt`: ensamblar las tres piezas
--
-- ax14 : ∀n. (√n)² ≤ n        ⚠️ `le` es una DISYUNCIÓN, no una desigualdad estricta
-- ax15 : ∀n. n < (σ√n)²
--
-- Con k = Nat.sqrt n, la tricotomía de `√n̄` contra `k̄` da dos ramas malas:
--   · `s < k̄`  ⇒ σs ≤ k̄ ⇒ (σs)² ≤ k̄² ≤ n̄,  contra ax15 (`n̄ < (σs)²`)
--   · `k̄ < s`  ⇒ σk̄ ≤ s ⇒ (σk̄)² ≤ s² ≤ n̄,  contra `n < (k+1)²` del meta
--
-- ⇒ hacen falta TRES auxiliares sobre `≤` —que aquí es `lt p q ∨ p = q`— y ninguno es
-- profundo: salen de `ltI_trans`, `ltI_mul_self` y `ltI_irrefl`, que ya están.
--
-- Uso: lake env lean sondeos/sqrt2_probe.lean

import PeanoRF.HA.Order
open FOL PeanoRF.Calculus ROBINSON_PlusPlus.Minimal.Axioms
namespace PeanoRF.HA

set_option autoImplicit false
set_option linter.unusedSimpArgs false

variable {Γ : List Formula}

/-! ## Resultado

    🏁 **SALIÓ**, y el cuerpo está en `PeanoRF/HA/Order.lean` §10–§11:
    `notI_lt_of_le` · `leI_mul_self` · `leI_trans` · `ax14I` · `ax15I` · **`numeralI_sqrt`**.
    Repetirlo aquí lo declararía dos veces y no compilaría.

    ⚠️ **El núcleo de Lean no trae `Nat.sqrt`** —vive en Mathlib, que aquí no hay—, así que
    `numeralI_sqrt` toma `k` y sus dos cotas como hipótesis. Es más general, y separa la
    aritmética del meta de la derivación del objeto. La función `isqrt` con sus dos cotas
    hace falta aparte, y sólo para EVALUAR dentro de `numOf_of_…`. -/

end PeanoRF.HA

#print axioms PeanoRF.HA.numeralI_sqrt
#print axioms PeanoRF.HA.leI_trans

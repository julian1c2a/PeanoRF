-- SONDEO 2026-09-22 — `√`, la última casilla de ADR-037: las TRES PIEZAS
--
-- `√` se caracteriza por DOS desigualdades:
--   ax14 : ∀n. (√n)² ≤ n        (`le`, o sea una DISYUNCIÓN)
--   ax15 : ∀n. n < (σ√n)²
--
-- ⇒ hace falta (a) DISCRECIÓN del orden —`a < b → σa ≤ b`— y (b) monotonía del CUADRADO.
--
-- ⛔⛔ **Y la puerta NO era la que yo dije.** Anuncié que hacía falta la forma ∀ de
-- `zeroI_or_succ`, para poder instanciarla en el testigo de un `elim_ex` —que es una
-- variable y no un término anclado—. **No hace falta ninguna forma ∀**: la discreción sale
-- de la tricotomía sobre `σa` vs `b`, que están los DOS anclados, refutando la tercera rama
-- con `notI_add_succ_self`, que ya estaba en producción desde el día anterior.
--
-- 🏁 Las tres piezas SALIERON, y están en `PeanoRF/HA/Order.lean` (§8 y §9):
--   `notI_lt_succ_of_lt` · `ltI_succ_le` (discreción) · `ltI_mul_self` (cuadrado)
--
-- ⚠️ Por eso este fichero se quedó SIN el cuerpo: repetirlo aquí sería declarar dos veces
-- lo mismo y no compilaría. Conserva lo que producción NO tiene: la medición del PASO 0,
-- que es lo que destrabó todo lo demás.
--
-- Uso: lake env lean sondeos/sqrt_probe.lean

import PeanoRF.HA.Order
open FOL PeanoRF.Calculus ROBINSON_PlusPlus.Minimal.Axioms
namespace PeanoRF.HA

set_option autoImplicit false
set_option linter.unusedSimpArgs false

variable {Γ : List Formula}

local macro "memA" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-! ## Paso 0 · el `Grounded` que sobraba, y llevaba un día de más

    `addI_assoc` y `mulI_distrib` pedían que el primer argumento estuviera ANCLADO. No hacía
    falta: el estorbo era el doble levantamiento que deja `forall_3`
    —`substTerm 1 (liftTerm 0 u) (liftTerm 0 (liftTerm 0 t))`—, y **aguas arriba existe el
    lema que lo deshace**, `FOL.substTerm_liftLift`, en el MISMO fichero que
    `substTerm_liftTerm`, que sí se estaba usando.

    🔑 Una hipótesis de más durante un día por no haber mirado el fichero entero. Y no era
    cosmética: sin quitarla `ltI_mul_self` **no se puede escribir**, porque sus asociaciones
    caen sobre términos con variables (`b·#0`, `a·σ#0`) que no están anclados. -/

example (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t u v : Term) :
    Γ ⊢ᵢ Formula.eq (add (add t u) v) (add t (add u v)) := by
  have h := specI (specI (specI (hΓ ax7_add_assoc (by memA)) t) u) v
  simpa (config := { decide := true }) only [ax7_add_assoc, forall_3, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, add,
    substTerm_liftTerm, substTerm_liftLift] using h

example (hΓ : ∀ g, List.Mem g arithAxioms → Γ ⊢ᵢ g) (t u v : Term) :
    Γ ⊢ᵢ Formula.eq (mul t (add u v)) (add (mul t u) (mul t v)) := by
  have h := specI (specI (specI (hΓ ax12_mul_distrib (by memA)) t) u) v
  simpa (config := { decide := true }) only [ax12_mul_distrib, forall_3, substFormula,
    substTerms, substTerm, ite_true, ite_false, Nat.reduceAdd, mul, add,
    substTerm_liftTerm, substTerm_liftLift] using h

end PeanoRF.HA

#print axioms PeanoRF.HA.notI_lt_succ_of_lt
#print axioms PeanoRF.HA.ltI_succ_le
#print axioms PeanoRF.HA.ltI_mul_self

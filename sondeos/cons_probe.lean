-- SONDEO 2026-09-22 — ¿cae `::` por COMPOSICIÓN, ahora que `/₂` está determinado?
--
-- ADR-037 bloqueó `::` con esta razón: «`pair` usa `/₂` (medido)». Y en RPP:
--
--   pair x y        = cantor_func x y = div2 (cantor_poly x y)
--   cantor_poly x y = (x+y)·σ(x+y) + 2·y          -- sólo +, ·, σ, 2
--   ax_L0_cons_def  : ∀x∀y.  x :: y = pair x (σy)
--
-- ⇒ si `/₂ n̄` es demostrablemente un numeral —y desde ADR-042 lo es—, entonces `m̄ :: n̄`
-- también, y **sin teoría nueva**: `cantor_poly` de numerales baja a numeral con
-- `numeralI_add`/`numeralI_mul`, y `numeralI_div2` cierra.
--
-- 🏁 **SALIÓ, a la primera.** El ⛔ de `::` cayó como COROLARIO del de `/₂`, y lo que se
-- construyó aquí está ya EN PRODUCCIÓN (ADR-044): `numeralI_cons`, `ax_L0I`, `consNat`,
-- `LQtdc`, `arithTDCAxioms` y `qDisjunctionProperty_arithTDC_final`, en `HA/Fragment.lean`
-- y `HA/Model.lean`.
--
-- ⚠️ Por eso este fichero se quedó SIN el cuerpo del sondeo: repetirlo aquí sería declarar
-- dos veces lo mismo y el sondeo no compilaría. Lo que conserva es la EVIDENCIA que lo
-- motivó —las tres identidades de definición que dicen que `pair` no es opaco— más la
-- medición del resultado.
--
-- Uso: lake env lean sondeos/cons_probe.lean

import PeanoRF.HA.Fragment
open FOL PeanoRF.Calculus ROBINSON_PlusPlus.Minimal.Axioms
namespace PeanoRF.HA

set_option autoImplicit false

/-! ## La evidencia: `pair` se DESARROLLA, no es opaco

    Las tres por `rfl`, que es lo que hace que el argumento de ADR-037 se pueda invertir:
    si `pair` fuese un símbolo primitivo con axiomas propios, `::` no saldría por
    composición de nada. -/

example : two = numeralM 2 := rfl

example (x y : Term) :
    pair x y = div2 (add (mul (add x y) (succ (add x y))) (mul two y)) := rfl

example (n : Nat) : numeralM (n + 1) = succ (numeralM n) := rfl

/-! ## El valor: `m̄ :: n̄` denota el emparejamiento de Cantor de `m` y `n+1` -/

example : consNat 0 0 = 2 := by decide
example : consNat 1 0 = 4 := by decide
example : consNat 0 1 = 5 := by decide

end PeanoRF.HA

#print axioms PeanoRF.HA.numeralI_cons

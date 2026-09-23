-- AUDITORÍA EXTERNA 2026-09-23 — re-medición contra aguas arriba
--
-- FOL @ 2d5b7c8  (sin cambios desde el 2026-09-22 12:04)
-- RPP @ e68354a  (DOCE commits nuevos: ADR-086…097)
--
-- ⚠️ Lo que había que mirar: RPP construyó el 2026-09-22 un MODELO ESTÁNDAR sobre `ℕ`
-- (`sondeos/ModeloNat.lean`, ADR-086/087) importando `FOL.Semantics` — **la misma
-- maquinaria que `PeanoRF/HA/Model.lean`**— y midió en ADR-088 que `Prf` NO es sólido
-- respecto de ese modelo. Había que comprobar si eso nos toca.
--
-- ✅ NO nos toca: `ax_list_induction` **no está en `coreAxioms`**, está en la lista
-- `omegaAxioms` del gate, y PeanoRF tiene **cero usos**. Nuestro modelo no usa ningún
-- esquema de inducción.
--
-- ⭐ Lo que SÍ nos toca, y es lo caro: **`consN_inj` ya está en producción de RPP**, y es
-- exactamente lo que ADR-046 dice que hay que construir para medir las listas.
--
-- Uso: lake env lean sondeos/audit_2026-09-23.lean

import PeanoRF.HA.Model
import ROBINSON_PlusPlus.Meta.CodeNatInjPrf

-- Lo nuestro, sin cambios tras los doce commits de RPP.
#print axioms PeanoRF.Calculus.derivesI_soundness
#print axioms PeanoRF.HA.qDisjunctionProperty_arithTDCS_final
#print axioms PeanoRF.HA.hcon_fragmentS
#print axioms PeanoRF.HA.numeralI_sqrt

-- Lo de RPP que podríamos consumir, y su precio: **ninguno**.
#print axioms ROBINSON_PlusPlus.Meta.CodeNumeralPrf.consN
#print axioms ROBINSON_PlusPlus.Meta.CodeNumeralPrf.two_mul_consN
#print axioms ROBINSON_PlusPlus.Meta.CodeNatInjPrf.consN_inj

namespace PeanoRF.HA
open ROBINSON_PlusPlus.Minimal.Axioms

-- ⭐ Y son EL MISMO número: su `consN` (sin división) y nuestro `consNat` (con ella).
example (a b : Nat) : consNat a b = ROBINSON_PlusPlus.Meta.CodeNumeralPrf.consN a b := by
  have h := ROBINSON_PlusPlus.Meta.CodeNumeralPrf.two_mul_consN a b
  simp only [consNat]
  omega

end PeanoRF.HA

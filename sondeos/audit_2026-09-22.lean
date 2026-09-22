-- AUDITORÍA EXTERNA 2026-09-22 — re-medición de PeanoRF contra aguas arriba MOVIDAS
--
-- FOL @ 2d5b7c8 («ModelG: el símbolo, parámetro también en la SEMÁNTICA», mismo día 12:04)
-- RPP @ 132f584 («ADR-085: M1-M4 salen las cuatro a favor», mismo día 15:10)
--
-- ⚠️ POR QUÉ: FOL generificó `Model (D)` a `ModelG (S D)`, y `PeanoRF/HA/Model.lean` usa
-- `Model Nat` DIRECTAMENTE. Es exactamente la clase de cambio que el 2026-09-21 dejó al
-- gate ciego ante `Derives₀` sin que este proyecto tocara una línea. La medición es la
-- única forma de saber si el `abbrev Model (D) := ModelG String D` nos deja intactos.
--
-- Resultado: **intactos**. Los siete footprints salen idénticos a los de antes del cambio.
--
-- Uso: lake env lean sondeos/audit_2026-09-22.lean

import PeanoRF.HA.Model
import PeanoRF.HA.Order

#print axioms PeanoRF.Calculus.derivesI_soundness
#print axioms PeanoRF.Calculus.derivesI_consistent
#print axioms PeanoRF.Calculus.derivesI_ne_derives0
#print axioms PeanoRF.HA.hcon_fragmentD
#print axioms PeanoRF.HA.qDisjunctionProperty_arithTD_final
#print axioms PeanoRF.HA.zeroI_or_succ
#print axioms PeanoRF.HA.numeralI_div2

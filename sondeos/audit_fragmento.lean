-- Medición del FRAGMENTO, en una sola pasada: los cinco escalones y lo que cada uno pide.
-- Uso: lake env lean sondeos/audit_fragmento.lean
import PeanoRF.HA.Model
namespace PeanoRF.HA
open ROBINSON_PlusPlus.Minimal.Axioms

-- Las cifras, verificadas por el kernel.
example : arithAxioms.length = 17 := rfl
example : arithTAxioms.length = 19 := rfl
example : arithTMAxioms.length = 22 := rfl
example : arithTDAxioms.length = 23 := rfl
example : arithTDCAxioms.length = 24 := rfl
example : arithTDCSAxioms.length = 26 := rfl
example : subAxioms.length = 27 := rfl
example : coreAxioms.length = 34 := rfl

end PeanoRF.HA

#print axioms PeanoRF.HA.qDisjunctionProperty_arithTDCS_final
#print axioms PeanoRF.HA.hcon_fragmentS
#print axioms PeanoRF.HA.numeralI_sqrt
#print axioms PeanoRF.HA.isqrt_le


-- Los símbolos que cada signatura admite, uno a uno y por `rfl`.
namespace PeanoRF.HA
open ROBINSON_PlusPlus.Minimal.Axioms

-- `LQpp`, la signatura COMPLETA de Q⁺⁺: catorce símbolos de función.
example : LQpp zero_sym 0 = true := rfl
example : LQpp nil_sym 0 = true := rfl
example : LQpp succ_sym 1 = true := rfl
example : LQpp sqrt_sym 1 = true := rfl
example : LQpp div2_sym 1 = true := rfl
example : LQpp mod2_sym 1 = true := rfl
example : LQpp pred_sym 1 = true := rfl
example : LQpp prodp_sym 1 = true := rfl
example : LQpp add_sym 2 = true := rfl
example : LQpp mul_sym 2 = true := rfl
example : LQpp pow_sym 2 = true := rfl
example : LQpp sub_sym 2 = true := rfl
example : LQpp cons_sym 2 = true := rfl
example : LQpp concat_sym 2 = true := rfl

-- `LQtdcs`, la del fragmento: DIEZ dentro…
example : LQtdcs zero_sym 0 = true := rfl
example : LQtdcs succ_sym 1 = true := rfl
example : LQtdcs add_sym 2 = true := rfl
example : LQtdcs mul_sym 2 = true := rfl
example : LQtdcs pow_sym 2 = true := rfl
example : LQtdcs pred_sym 1 = true := rfl
example : LQtdcs mod2_sym 1 = true := rfl
example : LQtdcs div2_sym 1 = true := rfl
example : LQtdcs cons_sym 2 = true := rfl
example : LQtdcs sqrt_sym 1 = true := rfl

-- …y CUATRO fuera.
example : LQtdcs sub_sym 2 = false := rfl
example : LQtdcs concat_sym 2 = false := rfl
example : LQtdcs prodp_sym 1 = false := rfl
example : LQtdcs nil_sym 0 = false := rfl

end PeanoRF.HA

-- SONDEO 2026-09-18 — ¿tiene HA la propiedad de disyunción sobre la sintaxis GENÉRICA?
--
-- `Term` de FOL es genérico: `.func s ts` con `s : String` CUALQUIERA. El lenguaje de Q⁺⁺
-- usa cinco símbolos, pero la sintaxis admite infinitos más. Y `elim_forall` instancia con
-- CUALQUIER término. La pregunta: ¿se puede instanciar la tricotomía con basura?
import PeanoRF.HA.Numerals
open FOL PeanoRF.Calculus ROBINSON_PlusPlus.Minimal.Axioms
namespace PeanoRF.HA

/-- Dos símbolos que NO son del lenguaje de Q⁺⁺. -/
def foo : Term := Term.func "foo" []
def bar : Term := Term.func "bar" []

/-- ⚠️ La tricotomía instanciada en basura ES derivable en HA. -/
theorem junk_trichotomy :
    ctx [] ⊢ᵢ Formula.or (lt foo bar)
                (Formula.or (Formula.eq foo bar) (lt bar foo)) := by
  have h19 : ctx [] ⊢ᵢ ax19_lt_trichotomy := ax' (by simp [coreAxioms])
  have h := specI (specI h19 foo) bar
  simp [substFormula, substTerm, substTerms, lt, foo, bar] at h
  exact h

end PeanoRF.HA
#print axioms PeanoRF.HA.junk_trichotomy

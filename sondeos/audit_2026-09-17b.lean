-- ════════════════════════════════════════════════════════════════════════════
-- AUDITORÍA 2026-09-17 (b) — ¿ALCANZA el criterio POR TIPO a lo aparecido hoy?
--
-- El gate se reescribió esa mañana: de lista POR NOMBRE a descubrimiento POR TIPO
-- (ADR-018). La pregunta de esta auditoría NO era si el control funciona —eso ya se
-- probó— sino **sobre cuánto del terreno actúa**, que es la pregunta que destapó el
-- agujero anterior.
--
-- 📏 LO MEDIDO (versión de la mañana, `List Formula → Formula → Prop`):
--      VE (6):    Derives 22 · Derives₀ 21 · Derivesᵢ 18 · Derives₁ 20 · Derives₂ 22
--                 · PrfH 8   ← de RPP, que nunca estuvo en ninguna lista: apareció sola
--      CIEGO (5): LK₀ 14 · LKc 15 · LKh 14 · Prf 7 · Prf₀ 17   = 67 constructores
--      Y los smoke tests `LK₀.ax` y `LKc.cut` PASABAN sin una palabra.
--
-- ⇒ ADR-018 (revisión b): el criterio pasa a TELESCOPIO. Este fichero es ahora la
--   CONTRAPRUEBA: con el mismo entorno, el gate tiene que ver las 11 y cazar los smokes.
-- ════════════════════════════════════════════════════════════════════════════
import Lean.Elab.Command
import FOL
import FOL.Sequent0          -- LK₀, LKc  : List Formula → List Formula → Prop
import FOL.Hauptsatz0        -- LKh       : Nat → List Formula → List Formula → Prop
import ROBINSON_PlusPlus.Meta.Hilbert            -- Prf₀, Prf : Formula → Prop
import ROBINSON_PlusPlus.Meta.HilbertDeduction   -- PrfH : List Formula → Formula → Prop
import PeanoRF.Meta.AxiomCheck

open Lean Elab Command

-- ── [1] EL INVENTARIO OFICIAL, con todos los cálculos en el entorno ──────────
-- Debe listar ONCE relaciones. Si vuelve a decir 6, la ceguera ha vuelto.

#assert_constructive_footprint

-- ── [2] SMOKE TESTS — la única prueba que vale: usarlos de verdad ────────────

/-- Un TEOREMA que usa un constructor de `LK₀`, cálculo de secuentes CLÁSICO
    (multiconclusión = clasicidad estructural). Antes de la revisión b: PASABA. -/
theorem smoke_lk0 (Γ Δ : List Formula) (A : Formula) (h1 : A ∈ Γ) (h2 : A ∈ Δ) : LK₀ Γ Δ :=
  LK₀.ax Γ Δ A h1 h2

#assert_no_forbidden_ctor smoke_lk0

/-- Un TEOREMA que usa `LKc.cut` — la regla de CORTE, que es lo que el Hauptsatz
    elimina. Tampoco está en `⊢ᵢ`. Antes de la revisión b: PASABA. -/
theorem smoke_lkc (Γ Δ : List Formula) (A : Formula)
    (h1 : LKc Γ (A :: Δ)) (h2 : LKc (A :: Γ) Δ) : LKc Γ Δ :=
  LKc.cut Γ Δ A h1 h2

#assert_no_forbidden_ctor smoke_lkc

/-- `PrfH.p3` **es** la doble negación clásica con otro nombre: `((A ⇒ ⊥) ⇒ ⊥) ⇒ A`.
    Ya se cazaba —`PrfH` tiene la forma reconocida— pero se clasificaba como
    FINITARIO/AJENO, y por eso la capa ω la daba por buena. Ahora: OBJETO. -/
theorem smoke_prfH (Γ : List Formula) (A : Formula) :
    ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH Γ
      (Formula.impl (Formula.impl (Formula.impl A Formula.bottom) Formula.bottom) A) :=
  ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.p3 Γ A

#assert_no_forbidden_ctor smoke_prfH

/-- Y el mismo DNE en `Prf`, que es Hilbert SIN contexto (`Formula → Prop`) ⇒ antes de
    la revisión b no tenía siquiera la forma que el gate reconocía. PASABA. -/
theorem smoke_prf (A : Formula) :
    ROBINSON_PlusPlus.Meta.Hilbert.Prf
      (Formula.impl (Formula.impl (Formula.impl A Formula.bottom) Formula.bottom) A) :=
  ROBINSON_PlusPlus.Meta.Hilbert.Prf.p3 A

#assert_no_forbidden_ctor smoke_prf

/-- Y el CONTRAEJEMPLO que evita que el control se vuelva vacuo por exceso: un teorema
    que usa `Derives₀.hyp` —nombre corto que SÍ está en `⊢ᵢ`— tiene que seguir PASANDO,
    o los puentes `derivesI_to_derives0` dejarían de compilar. -/
theorem smoke_puente (Γ : List Formula) (f : Formula) (h : f ∈ Γ) : Γ ⊢₀ f :=
  Derives₀.hyp Γ f h

#assert_no_forbidden_ctor smoke_puente

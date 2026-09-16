/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.DerivesI
import FOL.Soundness0

/-! # H3 · Solidez de `⊢ᵢ` — el espejo deja de ser metáfora

  **El teorema de transferencia.** De `Γ ⊢ᵢ f` se sigue que `f` es válida: verdadera en
  **todo** modelo de `Γ`, y en particular en el modelo estándar. Ése es el enunciado que
  convierte «espejo» en un hecho matemático, y el que `FOL.Derives` **no podía tener**
  (ADR-017).

  ## Por qué esto se puede escribir hoy y hace diez días no

  Aguas arriba apareció `derives0_soundness : Γ ⊢₀ f → Γ ⊨ f`, **en el build**. Como
  `derivesI_to_derives0` ya está probado, la solidez de `⊢ᵢ` es una composición.

  ## ⚠️ Enmienda de M-5, con la medición delante

  M-5 prohibía importar `FOL.Semantics` en bloque, y la razón medida el 2026-09-06 era que
  ahí vivía la mitad clásica de FOL. La medición del 2026-09-16 la matiza:

  | símbolo | footprint |
  |---|---|
  | `FOL.Metamath.Semantics.satisfies` | **ninguno** — la definición semántica es limpia |
  | `derives0_soundness` | `propext, Classical.choice, Quot.sound` |

  ⇒ Lo clásico **no está en la semántica, está en la PRUEBA**. Importar `Semantics` para
  usar `satisfies` no cuesta nada; usar `derives0_soundness` sí cuesta un `Classical.choice`
  heredado. `Completeness` y `Compacity` siguen prohibidas. Ver DECISIONS ADR-019.

  ## 🔭 La conjetura que esto deja abierta, y que merece la pena

  El `Classical.choice` de `derives0_soundness` es, muy probablemente, **el precio exacto de
  las tres reglas clásicas de `⊢₀`**: para justificar semánticamente `dne_rule`,
  `dne_schema` y `forall_not_ex_not` hace falta metateoría clásica. Nuestros 18
  constructores no las tienen.

  ⇒ **Conjetura**: una prueba DIRECTA de `derivesI_soundness` por inducción sobre `⊢ᵢ`
  (18 casos, ninguno clásico) tendría footprint `⊆ {propext, Quot.sound}` — constructiva.
  Sería el resultado propio más limpio del proyecto: *la solidez de la lógica intuicionista
  se demuestra intuicionistamente*, y el `Classical` de aguas arriba quedaría localizado en
  exactamente tres constructores.

  **Está sin probar.** Mientras tanto, lo de abajo hereda y la deuda queda contabilizada por
  el gate, que la distingue por procedencia.
-/

namespace PeanoRF.Calculus

open FOL

set_option autoImplicit false

/-- **Teorema de transferencia (heredado).** Lo intuicionistamente derivable es válido.

    ⚠️ Footprint: arrastra `Classical.choice` **de aguas arriba**, vía
    `derives0_soundness`. No es deuda nuestra (el gate lo clasifica por procedencia), pero
    cuenta — y la conjetura del encabezado dice que es evitable. -/
theorem derivesI_soundness {Γ : List Formula} {f : Formula} (h : Γ ⊢ᵢ f) :
    FOL.Metamath.Semantics.satisfies Γ f :=
  FOL.Metamath.Soundness0.derives0_soundness (derivesI_to_derives0 h)

/-- **Consistencia de `⊢ᵢ` desde el contexto vacío**: no se deriva `⊥` sin hipótesis.

    Es el primer corolario de la solidez y el que justifica todo lo demás: si `[] ⊢ᵢ ⊥`,
    entonces `⊥` sería verdadera en cualquier modelo, y basta exhibir uno. -/
theorem derivesI_consistent (h : ([] : List Formula) ⊢ᵢ Formula.bottom) : False := by
  have hv := derivesI_soundness h
  exact hv Unit { func := fun _ _ => (), rel := fun _ _ => True } (fun _ => ())
    (fun _ hf => absurd hf (List.not_mem_nil))

end PeanoRF.Calculus

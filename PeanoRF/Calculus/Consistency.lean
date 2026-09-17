/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Calculus.DerivesI
import FOL.Finitary0

/-! # La consistencia de `⊢ᵢ` **sin pasar por la semántica**

  `Calculus/Soundness.lean` ya da `derivesI_consistent`, pero por la **vía semántica**:
  si `[] ⊢ᵢ ⊥` entonces `⊥` sería verdadera en todo modelo, y no lo es. Funciona, y su
  footprint es limpio — pero para llegar necesita **un modelo**, es decir, presupone
  justamente la clase de objeto de la que la teoría formal pretende hablar.

  Aquí está el mismo enunciado por la vía **puramente sintáctica**: `⊢ᵢ → ⊢₀` (nuestro
  puente) compuesto con `FOL.Finitary0.derives0_consistent_fin`, que aguas arriba se
  demuestra pasando `Derives₀` a un cálculo de secuentes y comprobando que **ningún
  secuente sin corte concluye `⊥`**. En toda la cadena no aparece la palabra «modelo».

  | teorema | ruta | footprint |
  |---|---|---|
  | `derivesI_consistent` (`Soundness.lean`) | semántica: `satisfies` + un modelo | `propext, Quot.sound` |
  | **`consistI_syn` (aquí)** | **sintáctica**: puente + `LKc` sin corte | `propext, Quot.sound` |

  ⚠️ **La cifra NO mejora, y decirlo importa.** Las dos rutas miden lo mismo. Lo que cambia
  es de qué depende la prueba, que es una cuestión de fundamentos y no de aritmética de
  axiomas: `#print axioms` no distingue «usa un modelo» de «no lo usa». Es exactamente la
  misma clase de ceguera que M-11 —un footprint limpio no dice sobre qué se indujo— y la
  razón de que este módulo exista aunque la tabla salga empatada.

  ## ⛔ Lo que esto NO es

  **No es la consistencia de HA.** Es la de la LÓGICA: contexto vacío, sin los axiomas de
  `HA.ctx`. La consistencia de HA es el teorema de Gentzen y pide inducción hasta `ε₀`, que
  está **fuera** del núcleo finitario de este proyecto (ADR-016) y no va a entrar por aquí.
  Confundir las dos cosas sería exactamente el error que M-9 vigila: dar por demostrado de
  más justo en el sitio donde una demostración de más produce una inconsistencia.
-/

namespace PeanoRF.Calculus

open FOL

set_option autoImplicit false

/-- **Consistencia de `⊢ᵢ`, por la vía sintáctica.** Ni un modelo en toda la cadena.

    Mide `[propext, Quot.sound]`, igual que la versión semántica: lo que gana no es
    footprint, es no depender de la existencia de una estructura. -/
theorem consistI_syn : Not (([] : List Formula) ⊢ᵢ Formula.bottom) :=
  fun h => FOL.Finitary0.derives0_consistent_fin (derivesI_to_derives0 h)

/-- Y `⊢ᵢ` tampoco prueba un átomo suelto — o sea que no es trivial «por arriba».

    ⭐ Este enunciado no es decorativo: es **la mitad** de lo que hace falta para separar
    `⊢ᵢ` de `⊢₀`. Con la propiedad de disyunción (H3bis), de `[] ⊢ᵢ P ∨ ¬P` saldría
    `[] ⊢ᵢ P` o `[] ⊢ᵢ ¬P`; esto mata la primera rama. La segunda la mata `notNotP`. -/
theorem notP_syn : Not (([] : List Formula) ⊢ᵢ Formula.atom "P" []) :=
  fun h => FOL.Finitary0.derives0_not_P_fin (derivesI_to_derives0 h)

end PeanoRF.Calculus

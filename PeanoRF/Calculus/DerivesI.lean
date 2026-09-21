/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import PeanoRF.Prelim
import FOL.Derives0

/-! # `⊢ᵢ` — deducción natural INTUICIONISTA, finitaria y sin habitantes-axioma

  El cálculo **sujeto** de PeanoRF. Son los **18 constructores no clásicos** de
  `FOL.Derives₀`: los 21 suyos menos `dne_rule`, `dne_schema` y `forall_not_ex_not`.

  ## Por qué hace falta un cálculo propio

  Ninguno de los dos estratos de aguas arriba sirve para la tesis de este proyecto
  (`REFERENCE.md` §0bis de ROBINSON_PlusPlus; medido el 2026-09-16, revisado el 2026-09-17).
  ⚠️ Aguas arriba hay ya **cinco** nociones de derivabilidad: a las de abajo se suman
  `Derives₁` (sin `rewrite_at`) y `Derives₂` (sin `subst`), ambas **clásicas** y
  equivalentes a `Derives₀`. Ninguna es intuicionista ⇒ `⊢ᵢ` sigue sin duplicado:

  | | `FOL.Derives` (`⊢`) | `FOL.Derives₀` (`⊢₀`) | **`⊢ᵢ` (aquí)** |
  |---|---|---|---|
  | axiomas habitantes | ⛔ 7 | ✅ 0 | ✅ **0** |
  | inducción legítima (M-11) | ⛔ nunca | ✅ | ✅ |
  | finitario | ⛔ `gen_rule` es **constructor** | ✅ | ✅ |
  | solidez | ⛔ **imposible** | ✅ `derives0_soundness` | ✅ **heredada** |
  | lógica objeto | ⛔ **clásica por constructor** (desde 2026-09-17; antes, axiomas aparte) | ⛔ **clásica por constructor** | ✅ **intuicionista** |

  * **`Derives` no vale**: `FOL/cuarentena/Inconsistencia.lean` demuestra
    `inconsistencia_de_cualquier_solidez` — *cualquier* testigo del enunciado de solidez
    para `⊢` da `False`. Es HERRAMIENTA, no SUJETO (ADR-024 de RPP): de `axioms ⊢ φ` no se
    puede concluir que φ sea verdadera en ℕ₀, y ahí muere el espejo.
  * **`Derives₀` tampoco**: trae `dne_rule`, `dne_schema` y `forall_not_ex_not` **como
    constructores**, porque su cometido era la completitud, que es clásica. Adoptarlo
    haría de PeanoRF un espejo de PA, no de HA — contra M-1.

  ⇒ `⊢ᵢ` es `⊢₀` **menos esos tres**. No existe aguas arriba (comprobado), así que M-4 no
  lo prohíbe: es contenido nuevo, y es la tesis del proyecto hecha objeto matemático.

  ## Lo que se gana, y es casi todo

  El puente `derivesI_to_derives0` es una **inducción sobre `⊢ᵢ`** — legítima, porque no
  tiene habitantes-axioma. Componiéndolo con `derives0_soundness` (que está **en el
  build** aguas arriba) sale la solidez de `⊢ᵢ` **gratis**: ver `Calculus/Soundness.lean`.

  ## ⚠️ Lo que este módulo NO puede garantizar solo

  Que nadie use los tres constructores clásicos es una propiedad del **término de prueba**,
  y `#print axioms` es **CIEGO** a ella — igual que lo es a los habitantes-axioma (M-11 de
  RPP). Aquí la ceguera se evita por construcción: los tres no existen en `⊢ᵢ`. Pero en
  cuanto una prueba mezcle `⊢₀` y `⊢ᵢ`, hace falta el control de constructores del gate
  (`PeanoRF/Meta/AxiomCheck.lean`, eje objeto §constructores).
-/

namespace PeanoRF.Calculus

open FOL

set_option autoImplicit false

/-- **Deducción natural INTUICIONISTA de FOL⁼, finitaria y sin habitantes-axioma.**

    Los 18 constructores no clásicos de `FOL.Derives₀`. Se puede inducir sobre él. -/
inductive Derivesᵢ : List Formula → Formula → Prop where
  | hyp : ∀ Γ f, f ∈ Γ → Derivesᵢ Γ f

  -- Implicación
  | intro_impl : ∀ Γ A B, Derivesᵢ (A :: Γ) B → Derivesᵢ Γ (.impl A B)
  | elim_impl  : ∀ Γ A B, Derivesᵢ Γ (.impl A B) → Derivesᵢ Γ A → Derivesᵢ Γ B

  -- Conjunción
  | intro_and  : ∀ Γ A B, Derivesᵢ Γ A → Derivesᵢ Γ B → Derivesᵢ Γ (.and A B)
  | elim_and_l : ∀ Γ A B, Derivesᵢ Γ (.and A B) → Derivesᵢ Γ A
  | elim_and_r : ∀ Γ A B, Derivesᵢ Γ (.and A B) → Derivesᵢ Γ B

  -- Disyunción
  | intro_or_l : ∀ Γ A B, Derivesᵢ Γ A → Derivesᵢ Γ (.or A B)
  | intro_or_r : ∀ Γ A B, Derivesᵢ Γ B → Derivesᵢ Γ (.or A B)
  | elim_or    : ∀ Γ A B C, Derivesᵢ Γ (.or A B) → Derivesᵢ (A :: Γ) C → Derivesᵢ (B :: Γ) C →
      Derivesᵢ Γ C

  -- Cuantificadores. `intro_forall` ES la regla de la eigenvariable: el contexto se LEVANTA.
  | intro_forall : ∀ Γ A, Derivesᵢ (Γ.map (liftFormula 0)) A → Derivesᵢ Γ (.forall A)
  | elim_forall  : ∀ Γ A t, Derivesᵢ Γ (.forall A) → Derivesᵢ Γ (substFormula 0 t A)
  | intro_ex : ∀ Γ A t, Derivesᵢ Γ (substFormula 0 t A) → Derivesᵢ Γ (.ex A)
  | elim_ex  : ∀ Γ A B, Derivesᵢ Γ (.ex A) →
      Derivesᵢ (A :: Γ.map (liftFormula 0)) (liftFormula 0 B) → Derivesᵢ Γ B

  -- Ex falso quodlibet. ⚠️ Intuicionista: de ⊥ se sigue todo. NO es doble negación.
  | bot_elim : ∀ Γ A, Derivesᵢ Γ ⊥ → Derivesᵢ Γ A

  -- Debilitamiento
  | weakening : ∀ Γ Γ' f, Derivesᵢ Γ f → (∀ x, x ∈ Γ → x ∈ Γ') → Derivesᵢ Γ' f

  -- Reescritura en subexpresión exacta. `LocalRule` sólo tiene `commuteImpl`
  -- (`A ⇒ B ⇒ C` ↔ `B ⇒ A ⇒ C`), intuicionistamente válida: no cuela clasicidad.
  | rewrite_at : ∀ Γ f f' p sub sub',
      Derivesᵢ Γ f →
      getAt? f p = some sub →
      LocalRule sub sub' →
      f' = replaceAt f p sub' →
      Derivesᵢ Γ f'

  -- Igualdad
  | refl  : ∀ Γ t, Derivesᵢ Γ (.eq t t)
  | subst : ∀ Γ t₁ t₂ f, Derivesᵢ Γ (.eq t₁ t₂) → Derivesᵢ Γ (substFormula 0 t₁ f) →
      Derivesᵢ Γ (substFormula 0 t₂ f)

@[inherit_doc] infix:50 " ⊢ᵢ " => Derivesᵢ

/-- **El encaje**: todo lo intuicionistamente derivable lo deriva `⊢₀`.

    ⭐ La prueba es una **inducción sobre `⊢ᵢ`**, legítima porque no tiene
    habitantes-axioma (M-11). Cada caso es su constructor homónimo.

    ⚠️ La recíproca **NO vale, y a propósito**: `⊢₀` tiene las tres reglas clásicas. Esa
    asimetría **es** la tesis del proyecto — si el puente fuera una equivalencia, no
    habría nada que demostrar. -/
theorem derivesI_to_derives0 : ∀ {Γ : List Formula} {f : Formula}, (Γ ⊢ᵢ f) → (Γ ⊢₀ f) := by
  intro Γ f h
  induction h with
  | hyp Γ f hmem => exact Derives₀.hyp Γ f hmem
  | intro_impl Γ A B _ ih => exact Derives₀.intro_impl Γ A B ih
  | elim_impl Γ A B _ _ ih1 ih2 => exact Derives₀.elim_impl Γ A B ih1 ih2
  | intro_and Γ A B _ _ ih1 ih2 => exact Derives₀.intro_and Γ A B ih1 ih2
  | elim_and_l Γ A B _ ih => exact Derives₀.elim_and_l Γ A B ih
  | elim_and_r Γ A B _ ih => exact Derives₀.elim_and_r Γ A B ih
  | intro_or_l Γ A B _ ih => exact Derives₀.intro_or_l Γ A B ih
  | intro_or_r Γ A B _ ih => exact Derives₀.intro_or_r Γ A B ih
  | elim_or Γ A B C _ _ _ ih1 ih2 ih3 => exact Derives₀.elim_or Γ A B C ih1 ih2 ih3
  | intro_forall Γ A _ ih => exact Derives₀.intro_forall Γ A ih
  | elim_forall Γ A t _ ih => exact Derives₀.elim_forall Γ A t ih
  | intro_ex Γ A t _ ih => exact Derives₀.intro_ex Γ A t ih
  | elim_ex Γ A B _ _ ih1 ih2 => exact Derives₀.elim_ex Γ A B ih1 ih2
  | bot_elim Γ A _ ih => exact Derives₀.bot_elim Γ A ih
  | weakening Γ Γ' f _ hsub ih => exact Derives₀.weakening Γ Γ' f ih hsub
  | rewrite_at Γ f f' p sub sub' _ hget hrule heq ih =>
      exact Derives₀.rewrite_at Γ f f' p sub sub' ih hget hrule heq
  | refl Γ t => exact Derives₀.refl Γ t
  | subst Γ t₁ t₂ f _ _ ih1 ih2 => exact Derives₀.subst Γ t₁ t₂ f ih1 ih2

/-- Y de ahí a `⊢`, componiendo con el encaje de aguas arriba. Se expone por comodidad:
    permite consumir los teoremas de ROBINSON_PlusPlus **en la dirección correcta**
    (lo nuestro entra en su mundo; lo suyo NO entra en el nuestro).

    🏁 **ENTREGABLE**: nada del árbol lo usa, y está bien — es una puerta de salida
    para quien consuma esta librería, no una pieza interna. -/
theorem derivesI_to_derives {Γ : List Formula} {f : Formula} (h : Γ ⊢ᵢ f) : Γ ⊢ f :=
  -- ⚠️ `Derives₀` y su puente viven en la RAÍZ, no bajo `FOL` (`Derives0.lean` no abre
  -- namespace). De ahí el `_root_`.
  _root_.derives0_to_derives (derivesI_to_derives0 h)

end PeanoRF.Calculus

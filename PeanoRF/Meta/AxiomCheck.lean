/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- PeanoRF/Meta/AxiomCheck.lean
-- ════════════════════════════════════════════════════════════════════════════
-- Gate de compilación de la PUREZA CONSTRUCTIVA (MANDATORIES M-1 y M-2, ADR-013).
--
-- Vigila DOS EJES que no son el mismo, y esa distinción es la tesis del proyecto:
--
--   EJE OBJETO — la lógica FORMALIZADA es intuicionista.  DURO, sin excepciones.
--     Ninguna declaración propia puede depender de los axiomas CLÁSICOS de nivel
--     objeto de FOL. Medido 2026-09-06: son exactamente TRES, y en FOL solo se usan
--     desde la mitad modelo-teórica (Completeness/Compacity), que este proyecto no
--     importa. Es decir: hoy la distancia a violarlos es un `import` deliberado.
--
--   EJE META — las PRUEBAS EN LEAN son constructivas.  Diana `{propext, Quot.sound}`.
--     Aquí hay una deuda HEREDADA y con fecha de caducidad: `ROBINSON_PlusPlus` aún
--     no es constructivo a nivel meta (su conjunto `axioms` arrastra `Classical.choice`
--     por las primitivas `String` del núcleo de Lean 4.31, la trampa conocida de
--     `ite` sobre `String`). El autor la va a sanear aguas arriba. Mientras tanto se
--     tolera con AVISO y recuento, nunca en silencio: `metaDebtIsError := true` el día
--     que RPP esté limpio, y el gate pasa a exigir el footprint diana completo.
--
--     ⚠️ La tolerancia va por PROCEDENCIA, no por nombre de axioma. La primera versión
--     de este gate toleró `Classical.choice` a secas, y un smoke test con
--     `open Classical in ... em p` pasó como «deuda heredada»: el gate no mordía. Ahora
--     una declaración solo hereda deuda si el `Classical.choice` le entra ATRAVESANDO
--     una constante de `FOL`/`ROBINSON_PlusPlus`/`Peano` que ya lo arrastra. Si el
--     `Classical` lo mete nuestra propia prueba (vía `Init.*`, `by_cases` sin instancia
--     `Decidable`, `native_decide`…), es ERROR.
--
--   EJE FINITARIO — el cálculo es EFECTIVO: `⊢` recursivamente enumerable.  DURO en el
--     núcleo; permitido sólo bajo `PeanoRF.Omega.*`.
--     Este eje es INDEPENDIENTE del anterior y por eso hace falta aparte: `raa`, `gen`,
--     `or_elim`, `ex_elim` e `imp_intro` **no son clásicas** — son ω-reglas. Con ellas
--     `⊢` deja de ser r.e. y el sistema pasa a ser ω-lógica: «demostrabilidad = verdad en
--     el modelo estándar», como dice el propio docstring de `FOL/MetaRules.lean`. Un
--     sistema así da el espejo pero no da contenido fundacional ni meta-lenguaje: no hay
--     checker posible para una regla con infinitas premisas (ADR-016).
--
--     ⚠️ Y hay un peligro concreto, no teórico: `raa` e `imp_intro` toman premisas META
--     (`Γ ⊢ A → Γ ⊢ B`), que se cumplen VACÍAMENTE cuando la premisa no es derivable. En
--     cuanto este proyecto demuestre soundness de `Derives` hacia ℕ₀, un solo testigo de
--     no-derivabilidad `¬(axioms ⊢ ψ)` con ψ verdadera daría `axioms ⊢ ¬ψ` y, por
--     soundness, `¬⟦ψ⟧`: contradicción. ROBINSON_PlusPlus se salva porque enuncia Gödel
--     con `Prf` (aritmetizada, finitaria) y su puente `prf_to_derives` va en un solo
--     sentido — pero PeanoRF es justo el proyecto que fabricaría el ingrediente que falta.
--
-- Qué NO es clásico, y por eso NO se prohíbe POR EL EJE OBJETO (sí por el finitario):
--   • `FOL.MetaRules.raa` — es introducción de ¬ (`Γ ⊢ A → Γ ⊢ ⊥` ⟹ `Γ ⊢ ¬A`),
--     intuicionistamente válida pese a llamarse «reducción al absurdo».
--   • `FOL.MetaRules.gen` — ω-regla; no es clásica, es infinitaria.
--   • `FOL.MetaRules.{imp_intro, or_elim, ex_elim}` — reglas meta estructurales.
--
--   ⚠⚠ LA CEGUERA DE `#print axioms`, Y EL CUARTO CONTROL (2026-09-16)
--     `collectAxioms` ve AXIOMAS. No ve **constructores**. Y aguas arriba las dos reglas
--     que este gate existía para vigilar se han vuelto constructores:
--
--       • `FOL.Derives.gen_rule` — la ω-regla, antes el `axiom FOL.MetaRules.gen`.
--         `gen` pasó a tener footprint `[propext]` y **el eje finitario dejó de verla**:
--         el contador de la capa ω bajó de 5 a 4 usos y el gate siguió diciendo OK.
--       • `Derives₀.dne_rule` / `.dne_schema` / `.forall_not_ex_not` — las tres clásicas
--         de `Derives₀`, que son constructores desde su nacimiento.
--
--     Es el fallo de ADR-015 otra vez (un control que da VERDE sin comprobar), esta vez
--     por deriva aguas arriba y no por un error al escribirlo. ROBINSON_PlusPlus ya había
--     nombrado la causa general en su regla M-11: «`#print axioms` es CIEGO» a los
--     habitantes de un inductivo, y por eso tiene `check-estratos.bash` **además de**
--     `check-footprints.bash`. No son el mismo control y ninguno sustituye al otro.
--
--     ⇒ El cuarto control recorre el TÉRMINO DE PRUEBA (no el footprint) y prohíbe
--     constructores por nombre. Ver `forbiddenConstructors`.
--
-- El gate recorre TODA declaración propia (módulo bajo `PeanoRF.*`) vía
-- `Lean.collectAxioms`. Detecta el «Classical OCULTO» que `grep 'Classical\.'` no ve:
-- `by_cases`/`decide`/`omega`/`simp` sobre una proposición sin instancia `Decidable`
-- en contexto elaboran `Classical.propDecidable` sin que la palabra aparezca en el
-- código fuente.
-- ════════════════════════════════════════════════════════════════════════════

import Lean.Elab.Command
import Lean.Util.CollectAxioms

-- El barrido necesita ver TODAS las declaraciones propias: se importa aquí cada
-- módulo de la librería MENOS el barrel raíz `PeanoRF.lean` — que importa a este el
-- último — para evitar el ciclo. Añadir aquí cada módulo nuevo.
import PeanoRF.Prelim
import PeanoRF.Calculus.DerivesI
import PeanoRF.Calculus.Eq
import PeanoRF.Calculus.Soundness
import PeanoRF.Omega.Basic
import PeanoRF.HA.Axioms
import PeanoRF.HA.Arith

set_option autoImplicit false

namespace PeanoRF.Meta

open Lean Elab Command

-- ─────────────────────────────────────────────────────────────────
-- Configuración del gate
-- ─────────────────────────────────────────────────────────────────

/-- **EJE OBJETO.** Los axiomas CLÁSICOS de nivel objeto de FOL. Depender de
    cualquiera de ellos contradice la tesis del proyecto: no hay baseline ni
    excepción posible.

    Inventario medido el 2026-09-06 sobre FOL (13 `axiom` en total): estos tres son
    los clásicos; los otros diez son las cinco de completitud (fuera de nuestro import
    surface) y las cinco meta-reglas estructurales/infinitarias, que sí son
    intuicionistamente admisibles. -/
private def objectClassicalAxioms : List Name :=
  [ `FOL.MetaRules.dne                                  -- ¬¬A ⊢ A
  , `FOL.Theorems.Neg.dne                               -- idem, versión de Theorems
  , `FOL.Theorems.Quantifiers.forall_not_impl_exists_not -- ¬∀¬ ⊢ ∃
  ]

/-- **EJE META.** Footprint diana: los dos axiomas no-clásicos que Lean usa para
    proposiciones y cocientes. `sorryAx` se tolera aparte — el compilador ya avisa de
    cada `sorry`, y este gate no es un detector de `sorry`. -/
private def allowedAxioms : List Name := [``propext, ``Quot.sound, ``sorryAx]

/-- **EJE META — deuda HEREDADA, con fecha de caducidad.** Axiomas que hoy llegan
    inevitablemente desde aguas arriba y se toleran con AVISO:

    * `Classical.choice` — `ROBINSON_PlusPlus.Minimal.Axioms.axioms` (el conjunto de
      axiomas de Q⁺⁺) lo arrastra vía las funciones de codificación `strCodeM`,
      `termCodeM`, `formCodeM`, que usan primitivas `String` del núcleo de Lean 4.31.
      Medido: 44 de 313 declaraciones de `Minimal.Axioms` están afectadas, incluida
      `axioms` misma — o sea, **cualquier** teorema sobre Q⁺⁺ lo hereda hoy.
    * `ROBINSON_PlusPlus.Minimal.Axioms.ax_axiomsCodeT_eq` — el único `axiom` de Lean
      de RPP, sancionado y en su línea base.

    ⚠️ Esto NO es una excepción a la MANDATORY: es una deuda de una dependencia, que
    su autor va a saldar. Lo que el gate garantiza mientras tanto es que no aparezca
    ningún axioma no-constructivo NUEVO, y que la deuda sea visible y contable en cada
    build en vez de disolverse en el ruido. -/
private def inheritedMetaDebt : List Name :=
  [ ``Classical.choice
  , `ROBINSON_PlusPlus.Minimal.Axioms.ax_axiomsCodeT_eq
  ]

/-- **EJE FINITARIO.** Axiomas que rompen la efectividad de `⊢`. Dos familias:

    * Las **cinco meta-reglas ω de FOL**, cuyas premisas son meta-funciones Lean o
      infinitarias (`gen` es literalmente la ω-regla).
    * Los **cuatro meta-axiomas de ROBINSON_PlusPlus** que postulan `axioms ⊢ φ` para
      esquemas que Q⁺⁺ **no** demuestra (inducción, inducción de listas, alternancia mod 2,
      TFA). Bajo un `⊢` finitario esos enunciados son falsos; sólo son coherentes en la
      lectura ω. En PeanoRF la inducción **entra en el conjunto de axiomas**, no se
      postula como derivable de Q⁺⁺ (ADR-016).

    Medido 2026-09-06: 99 de 521 declaraciones de ROB++ (19 %) arrastran alguna. Por eso
    la capa `PeanoRF.Omega.*` existe — para reusarlas donde se quiera, marcadas. -/
private def omegaAxioms : List Name :=
  [ `FOL.MetaRules.imp_intro, `FOL.MetaRules.gen, `FOL.MetaRules.raa
  , `FOL.MetaRules.or_elim,   `FOL.MetaRules.ex_elim
  , `ROBINSON_PlusPlus.Full.ax_induction
  , `ROBINSON_PlusPlus.Full.ax_list_induction
  , `ROBINSON_PlusPlus.Full.ax_mod2_alternation
  , `ROBINSON_PlusPlus.Minimal.Theorems.Block8.ax_p_tfa
  ]

/-- La capa ω declarada: bajo este prefijo de módulo, `omegaAxioms` está permitido.
    Todo lo demás es núcleo finitario. -/
private def omegaLayer : Name := `PeanoRF.Omega

/-! ### CONTROL DE CONSTRUCTORES, POR TIPO — lo que `#print axioms` no puede ver

    ⚠⚠ **Reescrito el 2026-09-17 tras una auditoría.** La versión anterior era una lista
    de nombres, y caducó **tres veces en dos días**:

    1. `FOL.MetaRules.gen` pasó de axioma a constructor ⇒ el eje finitario dejó de verla.
    2. `Derives` movió sus reglas clásicas de axiomas de `MetaRules` a **constructores
       propios** (`Derives.dne_rule`, …) ⇒ sin vigilar.
    3. Aparecieron `Derives₁` y `Derives₂`, cada uno con **su propia copia** de las tres
       clásicas ⇒ sin vigilar. **9 de 12 constructores clásicos quedaron ciegos.**

    El defecto no era la lista: era su **polaridad**. Una lista de prohibidos deja pasar
    todo lo que no nombra, y aguas arriba crece más rápido de lo que se actualiza.

    ## El criterio, ahora estructural

    1. Se **descubren por TIPO** todas las relaciones de derivabilidad del entorno: los
       inductivos de tipo `List Formula → Formula → Prop`. Es el mismo criterio que usa
       `check-estratos.bash` de ROBINSON_PlusPlus — clasificar por el TIPO, no por el
       nombre — y por eso un cálculo nuevo **aparece solo**.
    2. Se toman los constructores de **nuestro** `Derivesᵢ` como referencia.
    3. **Cualquier constructor de otro cálculo cuyo nombre corto NO esté entre los de
       `Derivesᵢ` es una regla que nosotros NO tenemos** ⇒ prohibido en el núcleo.

    ⇒ **El silencio significa PROHIBIDO, no permitido.** Un `Derives₃` futuro entra
    vigilado por defecto, sin tocar este fichero.

    ⚠️ Los puentes (`derivesI_to_derives0`) usan `Derives₀.hyp`, `Derives₀.intro_impl`…
    y **pasan**, porque esos nombres cortos SÍ están en `Derivesᵢ`. Lo que no pasa es
    justo lo que `⊢ᵢ` no tiene.-/

/-- Nombres cortos de los constructores CLÁSICOS de nivel objeto. Prohibidos **en todas
    partes, incluida la capa ω**: son la tesis (M-1), no una cuestión de efectividad.
    Se comparan por nombre CORTO, así que cubren los cuatro cálculos a la vez y los que
    vengan. -/
private def classicalCtorShortNames : List Name :=
  [`dne_rule, `dne_schema, `forall_not_ex_not]

/-- Excepciones conscientes: constructores ajenos que **no** están en `Derivesᵢ` pero se
    aceptan igualmente. **Vacía**, y cada entrada necesitará su justificación escrita.
    Candidato previsible: las congruencias primitivas de `Derives₂`, que sustituyen a
    `subst` y no son clásicas. -/
private def benignForeignCtors : List Name := []

/-- ¿Es `iv` una **relación de derivabilidad**? Criterio por TIPO:
    `List Formula → Formula → Prop`. -/
private def isDerivRelation (iv : InductiveVal) : Bool :=
  match iv.type with
  | .forallE _ t1 (.forallE _ t2 (.sort lvl) _) _ =>
      lvl.isZero && t1.isAppOf `List && t2.isConstOf `Formula
  | _ => false

/-- Todas las relaciones de derivabilidad del entorno, descubiertas por tipo. -/
private def derivRelations : CommandElabM (Array InductiveVal) := do
  let env ← getEnv
  let mut out : Array InductiveVal := #[]
  for (_, info) in env.constants.toList do
    if let .inductInfo iv := info then
      if isDerivRelation iv then out := out.push iv
  return out

/-- Nombres CORTOS de los constructores de nuestro `Derivesᵢ`: la referencia. -/
private def ownCtorShortNames : CommandElabM (Array Name) := do
  let env ← getEnv
  match env.find? `PeanoRF.Calculus.Derivesᵢ with
  | some (.inductInfo iv) => return iv.ctors.toArray.map (fun c => c.componentsRev.head!)
  | _ => throwError "el gate no encuentra `PeanoRF.Calculus.Derivesᵢ` — \
      ¿se ha renombrado el cálculo? El control de constructores depende de él."

/-- Constructores AJENOS prohibidos, calculados: los de cualquier otra relación de
    derivabilidad cuyo nombre corto no esté entre los de `Derivesᵢ`. -/
private def foreignForbiddenCtors : CommandElabM (Array (Name × Bool)) := do
  let own ← ownCtorShortNames
  let rels ← derivRelations
  let mut out : Array (Name × Bool) := #[]
  for iv in rels do
    if iv.name == `PeanoRF.Calculus.Derivesᵢ then continue
    for c in iv.ctors do
      let short := c.componentsRev.head!
      if own.contains short then continue
      if benignForeignCtors.contains c then continue
      -- el Bool dice si es CLÁSICO de nivel objeto (prohibido también en la capa ω)
      out := out.push (c, classicalCtorShortNames.contains short)
  return out


/-- Prefijos de módulo de las dependencias sibling. Un axioma no-constructivo solo se
    considera HEREDADO si entra a través de una constante definida en uno de estos
    módulos. El núcleo de Lean (`Init.*`, `Std.*`) **no** está aquí a propósito:
    `Classical.em` vive ahí, y usarlo es una decisión nuestra, no una herencia. -/
private def dependencyRoots : List Name := [`FOL, `ROBINSON_PlusPlus, `Peano]

/-- Poner a `true` cuando `ROBINSON_PlusPlus` sea constructivo a nivel meta: la deuda
    heredada pasa de AVISO a ERROR y el gate exige el footprint diana completo. -/
private def metaDebtIsError : Bool := false

/-- Excepciones propias documentadas (símbolos NUESTROS con footprint no-constructivo
    que se aceptan por una razón escrita). **Vacía**, y el objetivo es que siga así:
    cada entrada aquí necesita justificación en `DECISIONS.md`. -/
private def baselineOwn : List Name := []

-- ─────────────────────────────────────────────────────────────────
-- Herramienta puntual
-- ─────────────────────────────────────────────────────────────────

-- ──────────────────────────────────────────────────────────────
-- Procedencia: ¿la suciedad entra por una dependencia, o la metemos nosotros?
-- ──────────────────────────────────────────────────────────────

/-- ¿Está la constante definida en un módulo de la librería propia? -/
private def isOwn (env : Environment) (mods : Array Name) (n : Name) : Bool :=
  match env.const2ModIdx[n]? with
  | some idx => (`PeanoRF).isPrefixOf mods[idx.toNat]!
  | none     => false

/-- ¿Está la constante definida en un módulo de una dependencia sibling? -/
private def isDependency (env : Environment) (mods : Array Name) (n : Name) : Bool :=
  match env.const2ModIdx[n]? with
  | some idx => dependencyRoots.any (fun r => r.isPrefixOf mods[idx.toNat]!)
  | none     => false

/-- Constantes que `n` referencia directamente (en su tipo y en su valor). -/
private def directRefs (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none      => #[]
  | some info =>
    let fromType := info.type.getUsedConstants
    -- ⚠️⚠️ NO usar `info.value?`: para TEOREMAS devuelve `none` en Lean 4.31, así que el
    -- recorrido veía sólo los TIPOS y no los términos de prueba. Eso dejaba ciegos a la vez
    -- el control de procedencia y el de constructores — es decir, casi todo, porque casi
    -- todo lo que se vigila son teoremas. Se destapó el 2026-09-16 al ver que
    -- `derivesI_soundness` no reconocía su `Classical.choice` como heredado.
    -- El smoke test de ADR-018 no lo cogió porque usaba `def`, cuyo valor SÍ está.
    -- Lección: un smoke test tiene que usar la MISMA clase de declaración que se vigila.
    let fromVal := match info with
                   | .thmInfo v  => v.value.getUsedConstants
                   | .defnInfo v => v.value.getUsedConstants
                   | _           => #[]
    fromType ++ fromVal

/-- FRONTERA de `n`: se camina hacia atrás **solo por declaraciones propias**, y se
    devuelven las constantes ajenas que se tocan. Si alguna de esas constantes
    pertenece a una dependencia sibling y ya arrastra `ax`, entonces `ax` le llega a
    `n` HEREDADO. Si no, se lo ha metido nuestra propia prueba.

    El recorrido va acotado (`fuel`): un gate no puede colgar un build. -/
private def frontierOf (n : Name) : CommandElabM NameSet := do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut work : Array Name := #[n]
  let mut seen : NameSet := {}
  let mut frontier : NameSet := {}
  for _ in [0 : 20000] do
    if work.isEmpty then break
    let cur := work.back!
    work := work.pop
    if seen.contains cur then continue
    seen := seen.insert cur
    for r in directRefs env cur do
      if isOwn env mods r then
        unless seen.contains r do work := work.push r
      else
        frontier := frontier.insert r
  return frontier

private def inheritsFromDependency (ax : Name) (n : Name) : CommandElabM Bool := do
  let env ← getEnv
  let mods := env.header.moduleNames
  let frontier ← frontierOf n
  for c in frontier.toList do
    if isDependency env mods c then
      let axs ← collectAxioms c
      if axs.contains ax then return true
  return false

/-- **El cuarto control**: qué constructores prohibidos aparecen en el término de prueba.

    Un constructor es una constante ajena (vive en el inductivo de FOL), así que cae en la
    FRONTERA del recorrido — el mismo que usa la procedencia. Por eso este control sale
    casi gratis una vez `frontierOf` existe. -/
private def forbiddenCtorsUsed (n : Name) : CommandElabM (Array (Name × Bool)) := do
  let frontier ← frontierOf n
  let forbidden ← foreignForbiddenCtors
  return forbidden.filter (fun e => frontier.contains e.1)

-- ──────────────────────────────────────────────────────────────
-- Herramienta puntual
-- ──────────────────────────────────────────────────────────────

/-- Falla si la declaración depende de `Classical.choice`. Útil para comprobar un
    símbolo concreto mientras se trabaja; el gate real es el barrido de abajo. -/
elab "#assert_no_classical " id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let axioms ← Lean.collectAxioms name
  if axioms.contains ``Classical.choice then
    throwError "'{name}' depende de Classical.choice — reescribir constructivamente (ADR-013)"

/-- Falla si la declaración depende de un axioma clásico de NIVEL OBJETO. -/
elab "#assert_intuitionistic " id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let axioms ← Lean.collectAxioms name
  for a in objectClassicalAxioms do
    if axioms.contains a then
      throwError "'{name}' usa el axioma CLÁSICO de nivel objeto '{a}' — \
        contradice la tesis del proyecto (ADR-013, M-1). No hay excepción posible."

-- ─────────────────────────────────────────────────────────────────
-- Gate exhaustivo
-- ─────────────────────────────────────────────────────────────────

/-- Falla si la declaración depende de una ω-regla o meta-axioma (eje finitario). -/
elab "#assert_finitary " id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let axioms ← Lean.collectAxioms name
  for a in omegaAxioms do
    if axioms.contains a then
      throwError "'{name}' usa la ω-regla / meta-axioma '{a}' — el núcleo de PeanoRF es         FINITARIO (M-7, ADR-016). Usar el constructor de `Derives` correspondiente, o         mover la declaración a la capa `PeanoRF.Omega.*`."

/-- Falla si la declaración usa un constructor prohibido (control de CONSTRUCTORES). -/
elab "#assert_no_forbidden_ctor " id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let used ← forbiddenCtorsUsed name
  unless used.isEmpty do
    throwError "'{name}' usa {used.size} constructor(es) que `⊢ᵢ` NO tiene: \
      {used.toList.map (fun e => e.1)}. `#print axioms` NO ve esto."

/-- Barrido de TODA declaración propia de `PeanoRF`:

    * cualquier axioma clásico de nivel objeto ⟹ **error** (eje objeto, sin baseline);
    * cualquier axioma fuera de `allowedAxioms` ⟹ **error**, salvo que esté en
      `inheritedMetaDebt` (⟹ aviso con recuento, o error si `metaDebtIsError`) o el
      símbolo esté en `baselineOwn`;
    * avisa si una entrada de `baselineOwn` ya está limpia, para retirarla. -/
elab "#assert_constructive_footprint" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut scanned : Nat := 0
  let mut objectViolations : Array (Name × Name) := #[]
  let mut omegaViolations : Array (Name × Name) := #[]
  let mut ctorViolations : Array (Name × Name × String) := #[]
  let mut omegaLayerUses : Nat := 0
  let mut metaViolations : Array (Name × Name) := #[]
  let mut debtCarriers : Array Name := #[]
  let mut staleBaseline : Array Name := #[]
  for (name, _info) in env.constants.toList do
    if name.isInternalDetail then continue
    let some modIdx := env.const2ModIdx[name]? | continue
    let declMod := mods[modIdx.toNat]!
    unless (`PeanoRF).isPrefixOf declMod do continue
    scanned := scanned + 1
    let axs ← collectAxioms name
    -- eje objeto: duro, sin excepción
    for a in objectClassicalAxioms do
      if axs.contains a then objectViolations := objectViolations.push (name, a)
    -- eje finitario: duro fuera de la capa ω declarada
    let inOmegaLayer := omegaLayer.isPrefixOf declMod
    for a in omegaAxioms do
      if axs.contains a then
        if inOmegaLayer then omegaLayerUses := omegaLayerUses + 1
        else omegaViolations := omegaViolations.push (name, a)
    -- CONTROL DE CONSTRUCTORES (lo que el footprint no ve)
    for (ctor, esClasico) in ← forbiddenCtorsUsed name do
      -- Los CLÁSICOS de nivel objeto no se toleran en ninguna parte (M-1, es la tesis).
      -- El resto —ω-reglas y cualquier regla que `⊢ᵢ` no tenga— sólo en la capa ω.
      unless (!esClasico) && inOmegaLayer do
        let eje := if esClasico then "OBJETO" else "FINITARIO/AJENO"
        ctorViolations := ctorViolations.push (name, ctor, eje)
    -- eje meta
    let bad := axs.filter (fun a =>
      !allowedAxioms.contains a && !objectClassicalAxioms.contains a && !omegaAxioms.contains a)
    -- Clasificación por PROCEDENCIA, no por nombre: un axioma de la lista de deuda
    -- solo cuenta como heredado si de verdad entra por una dependencia sibling.
    let mut inherited : Array Name := #[]
    let mut own : Array Name := #[]
    for a in bad do
      if inheritedMetaDebt.contains a && (← inheritsFromDependency a name) then
        inherited := inherited.push a
      else
        own := own.push a
    unless inherited.isEmpty do debtCarriers := debtCarriers.push name
    if bad.isEmpty then
      if baselineOwn.contains name then staleBaseline := staleBaseline.push name
    else unless baselineOwn.contains name do
      for a in own do metaViolations := metaViolations.push (name, a)
      if metaDebtIsError then
        for a in inherited do metaViolations := metaViolations.push (name, a)
      pure ()
  unless staleBaseline.isEmpty do
    logWarning m!"[gate] {staleBaseline.size} excepción(es) de `baselineOwn` ya están LIMPIAS — retirarlas:\n{staleBaseline.toList}"
  unless objectViolations.isEmpty do
    throwError m!"[gate · EJE OBJETO] {objectViolations.size} uso(s) de lógica CLÁSICA de nivel objeto:\n\
      {objectViolations.toList}\n\
      → La lógica formalizada es INTUICIONISTA (M-1, ADR-013). Esto no tiene baseline: \
      reformular la prueba sin eliminación de doble negación."
  unless ctorViolations.isEmpty do
    throwError m!"[gate · CONSTRUCTORES] {ctorViolations.size} uso(s) de constructores \
      prohibidos — esto `#print axioms` NO lo ve:\n{ctorViolations.toList}\n\
      → El núcleo usa `PeanoRF.Calculus.Derivesᵢ`, que no tiene ni la ω-regla ni las \
      tres reglas clásicas. Si de verdad hace falta una, la declaración va a \
      `PeanoRF.Omega.*` (y sólo vale para las ω, no para las clásicas)."
  unless omegaViolations.isEmpty do
    throwError m!"[gate · EJE FINITARIO] {omegaViolations.size} uso(s) de ω-reglas o       meta-axiomas fuera de la capa `PeanoRF.Omega.*`:\n{omegaViolations.toList}\n      → El núcleo de PeanoRF es HA finitaria (M-7, ADR-016): `⊢` tiene que seguir siendo       r.e. Sustitutos finitarios: `imp_intro`→`Derives.intro_impl`, `raa`→`intro_impl`       (¬A = A⇒⊥), `or_elim`→`Derives.elim_or`, `ex_elim`→`Derives.elim_ex`,       `gen`→`Derives.intro_forall`. Y la inducción va EN EL CONJUNTO DE AXIOMAS, no       postulada como derivable de Q⁺⁺."
  unless metaViolations.isEmpty do
    throwError m!"[gate · EJE META] {metaViolations.size} axioma(s) no-constructivo(s) fuera de \
      la diana propext + Quot.sound:\n{metaViolations.toList}\n\
      → reescribir constructivamente (`Decidable.byContradiction`, `by_cases` sobre una \
      instancia `Decidable`, `decidable_of_iff`); medidas de terminación LEXICOGRÁFICAS, \
      nunca aritméticas ponderadas — estas últimas introducen `Classical.choice`."
  unless debtCarriers.isEmpty do
    logWarning m!"[gate · deuda META heredada] {debtCarriers.size} declaración(es) heredan \
      `Classical.choice`/axiomas sancionados de ROBINSON_PlusPlus. Es deuda AGUAS ARRIBA, \
      no nuestra — pero cuenta: cuando RPP se sanee, poner `metaDebtIsError := true`."
  -- INVENTARIO: que un cálculo nuevo aguas arriba se VEA, en vez de pasar inadvertido.
  -- Ésta es la mitad del arreglo que la lista por nombre no podía dar: la otra es que el
  -- silencio signifique prohibido.
  let rels ← derivRelations
  let fbd ← foreignForbiddenCtors
  logInfo m!"[gate · inventario] {rels.size} relaciones de derivabilidad detectadas POR TIPO: \
    {rels.toList.map (fun iv => iv.name)} ⇒ {fbd.size} constructores ajenos vigilados, \
    de ellos {(fbd.filter (fun e => e.2)).size} clásicos de nivel objeto."
  logInfo m!"[gate] OK — {scanned} declaraciones propias verificadas. \
    Eje objeto: intuicionista puro (axiomas Y constructores). Eje finitario: núcleo r.e. \
    ({omegaLayerUses} uso(s) de ω en la capa `PeanoRF.Omega`). \
    Eje meta: ⊆ propext + Quot.sound (+ {debtCarriers.size} con deuda heredada de RPP)."

-- ─────────────────────────────────────────────────────────────────
-- Verificaciones puntuales (H2)
-- ─────────────────────────────────────────────────────────────────
-- El barrido de abajo ya las cubre, pero dejarlas nombradas documenta la afirmación
-- central de H2: `zero_add` está probado SIN ω-reglas y SIN `ax_induction`.
#assert_finitary PeanoRF.HA.zero_add
#assert_intuitionistic PeanoRF.HA.zero_add
#assert_finitary PeanoRF.HA.induction_object
#assert_finitary PeanoRF.HA.gen_closed

#assert_constructive_footprint

end PeanoRF.Meta

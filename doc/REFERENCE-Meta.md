# REFERENCE · Meta — contacto, gate de pureza y capa ω

**Last updated:** 2026-09-22
**Autor**: Julián Calderón Almendros

> **Nodo temático del sistema REFERENCE** (AI-GUIDE §0.5).
> ⬆️ Índice raíz: **[REFERENCE.md](../REFERENCE.md)** · catálogo de los 18 módulos, grafo de
> dependencias y teoremas de cabecera.
> ↔️ Nodos hermanos: **[REFERENCE-Calculus.md](REFERENCE-Calculus.md)** (el cálculo `⊢ᵢ` y la
> barra de Kleene) · **[REFERENCE-HA.md](REFERENCE-HA.md)** (la Aritmética de Heyting).

---

## 1. Qué cubre este nodo

La **infraestructura**: el módulo de contacto con las tres dependencias, el gate de pureza
que decide si el proyecto cumple la directiva fundacional, y la capa donde vive —aislada y
contada— la ω-lógica.

| módulo | qué es | § |
|---|---|---|
| [`PeanoRF/Prelim.lean`](../PeanoRF/Prelim.lean) | el punto de contacto con FOL, ROB++ y `peanolib` | 2.1 |
| [`PeanoRF/Meta/AxiomCheck.lean`](../PeanoRF/Meta/AxiomCheck.lean) | **el gate de tres ejes**, en producción | 2.2 |
| [`PeanoRF/Omega/Basic.lean`](../PeanoRF/Omega/Basic.lean) | la capa ω, declarada y aislada | 2.3 |

⚠️ **`Prelim.lean` vive aquí y no en un nodo propio.** No es teoría: es la superficie de
importación, y la superficie de importación es asunto del gate — M-5 (qué se puede importar)
y el eje META (qué arrastra lo importado) se leen juntos o no se leen.

🔑 **La polaridad del gate, y es lo que hay que recordar**: comprueba los **axiomas** Y los
**constructores**, éstos **por telescopio**, y lo clásico lo decide el **TIPO** del
constructor, no su nombre. `raa` y `gen` **no** son clásicos pese a como suenan.

---

## 2. Módulos

## 2.1 `Prelim.lean`

**Fichero**: [`PeanoRF/Prelim.lean`](../PeanoRF/Prelim.lean)

**Namespace**: `PeanoRF.Prelim`
**Dependencies**: `FOL`, `ROBINSON_PlusPlus.Minimal.Axioms`, `Peano.PeanoNat.Axioms`
**Last updated**: 2026-09-06 14:00
**Status**: 🔄 In progress (sin declaraciones propias)
**@axiom_system**: FOL⁼ (vía `FOL`) + Q⁺⁺ (vía `ROBINSON_PlusPlus`)
**@importance**: high

Punto **único** de contacto con las librerías aguas arriba. Hoy no declara nada propio:
fija el *import surface* del proyecto y documenta por qué es el que es.

Dos decisiones que este módulo materializa, ambas con ADR:

* **No se redefine `ExistsUnique` ni la notación `∃!`/`∃¹`** — vienen de `Peano.Prelim`.
  Dos copias en dos namespaces son **dos constantes que no componen**, y el coste no se
  paga al escribirlas sino después, en puentes `rfl` por cada teorema que las cruce
  (ADR-010).
* **No se importan los barrels completos** de ROBINSON_PlusPlus ni de Peano, sino las
  capas concretas que se usan (ADR-012).

## 2.2 `Meta/AxiomCheck.lean`

**Fichero**: [`PeanoRF/Meta/AxiomCheck.lean`](../PeanoRF/Meta/AxiomCheck.lean)

**Namespace**: `PeanoRF.Meta`
**Dependencies**: `PeanoRF.Prelim`
**Last updated**: 2026-09-06 14:00
**Status**: ✅ Completo (gate en producción)
**@axiom_system**: n/a (metaprogramación)
**@importance**: high

Gate de compilación de las MANDATORIES M-1 y M-2 (ADR-013). Corre en **cada `lake build`**
y recorre toda declaración propia con `Lean.collectAxioms`. Vigila dos ejes:

| Eje | Qué exige | Severidad |
|---|---|---|
| **OBJETO** | Ninguna dependencia de `FOL.MetaRules.dne`, `FOL.Theorems.Neg.dne`, `FOL.Theorems.Quantifiers.forall_not_impl_exists_not` | error, sin baseline |
| **FINITARIO** | Ninguna dependencia de las 5 ω-reglas de FOL ni de los 4 meta-axiomas de ROB++ | error fuera de `PeanoRF.Omega.*`; recuento dentro |
| **META** | Footprint `⊆ {propext, Quot.sound}` (+`sorryAx`) | error; deuda heredada de RPP con aviso y recuento |

La deuda heredada se clasifica **por procedencia, no por nombre de axioma**: un
`Classical.choice` solo cuenta como heredado si entra atravesando una constante de
`FOL`/`ROBINSON_PlusPlus`/`Peano` (ver ADR-015 y el smoke test que lo destapó).

**Comandos que define**:

```lean
#assert_no_classical   <ident>   -- falla si el símbolo depende de Classical.choice
#assert_intuitionistic <ident>   -- falla si usa un axioma clásico de nivel objeto
#assert_finitary       <ident>   -- falla si usa una ω-regla o meta-axioma
#assert_constructive_footprint   -- el barrido exhaustivo (se invoca al final del módulo)
```

**Puntos de configuración** (todos `private`, documentados en el fichero):
`objectClassicalAxioms`, `allowedAxioms`, `inheritedMetaDebt`, `omegaAxioms`,
`omegaLayer`, `dependencyRoots`, `metaDebtIsError` (**`true` desde 2026-09-18**), `baselineOwn`,
`classicalCtorShortNames`, `benignForeignCtors`, `omegaAllowedForeignCtors`.

**Control de constructores, POR TELESCOPIO** (reescrito 2026-09-17, revisado esa misma
tarde; ADR-018). Descubre las relaciones de derivabilidad del entorno por su **tipo**:
inductivo **recursivo**, que menciona `Formula`, acaba en `Prop` y todos cuyos argumentos
son `Formula`, `List Formula` o `Nat`. Cubre deducción natural, secuentes de uno y dos
lados, cálculos con altura y Hilbert con o sin contexto. Prohibe en el núcleo **todo
constructor ajeno cuyo nombre corto no esté entre los de `Derivesᵢ`**, y marca como
**CLÁSICO por lo que la regla dice** — el patrón de la doble negación en el tipo del
constructor — no por cómo se llama. El silencio significa **prohibido**, también en la
capa ω, que ya no es comodín: necesita entrada explícita en `omegaAllowedForeignCtors`.
Publica en cada build un **inventario** con las relaciones detectadas y los
**casi-candidatos** que el telescopio rechazó, y su **ALCANCE**: los módulos propios que
tiene en el entorno. Esto último lo consume el control [E] de `check-doc-sync.bash`,
porque los imports de este fichero son una lista a mano y un módulo que no llegue hasta
aquí **no se vigila** sin que nada lo diga.

---

## 2.3 `Omega/Basic.lean`

**Fichero**: [`PeanoRF/Omega/Basic.lean`](../PeanoRF/Omega/Basic.lean)

**Namespace**: `PeanoRF.Omega`
**Dependencies**: `PeanoRF.Prelim`
**Last updated**: 2026-09-06 18:00
**Status**: ✅ Completo
**@axiom_system**: ω-lógica sobre Q⁺⁺ (**fuera** del núcleo HA)
**@importance**: high

**La capa ω declarada** (ADR-016). Todo lo que viva bajo `PeanoRF.Omega.*` está fuera del
núcleo finitario: el gate permite aquí las ω-reglas y las **cuenta** en cada build.

Expone cinco alias sancionados, para que toda dependencia de la capa ω sea visible en el
nombre: `gen`, `imp_intro`, `raa`, `or_elim`, `ex_elim`.

**Qué se pierde al cruzar la frontera**: en ω-lógica `⊢` no es r.e. Un teorema de esta capa
sirve para el espejo hacia Peano (ω-lógica es sólida para ℕ), pero **no** como contenido
fundacional ni como pieza del meta-lenguaje.

⚠️ **La regla que nunca debe cruzarse**: no demostrar soundness de `Derives` para
derivaciones con `raa`/`imp_intro` (M-9) — sus premisas META se cumplen vacíamente.

---

## 3. Lo que este nodo NO cubre

* el cálculo `⊢ᵢ`, su solidez y la barra de Kleene ⇒ **[REFERENCE-Calculus.md](REFERENCE-Calculus.md)**;
* los axiomas de HA, el dominio, el fragmento y el modelo ⇒ **[REFERENCE-HA.md](REFERENCE-HA.md)**;
* el grafo de dependencias completo y los teoremas de cabecera ⇒ **[REFERENCE.md](../REFERENCE.md)**.

---

⬆️ **[Volver al índice raíz](../REFERENCE.md)**

# Project Planning — PeanoRF

**Última actualización:** 2026-09-06 21:00
**Autor**: Julián Calderón Almendros

> Extensión de [NEXT-STEPS.md](NEXT-STEPS.md). Allí van las fases accionables a corto
> plazo; aquí el rumbo largo, la visión arquitectónica y el backlog.

---

## 1. Qué es este proyecto

**PeanoRF vuelca el proyecto Peano al lenguaje FOL⁼ + ROB++, de forma puramente
constructiva.** El resultado es un **espejo**: las propiedades que se demuestren para
PeanoRF se conservan en Peano.

No es una duplicación. Es una **división del trabajo**:

| | PeanoRF | Peano (`peanolib`) |
|---|---|---|
| Nivel | **objeto** — fórmulas de FOL⁼ y derivaciones | **meta** — tipos y funciones de Lean |
| Papel | **fundacional** | **computacional** |
| Naturales | términos del lenguaje aritmético | `ℕ₀`, tipo inductivo |
| Pregunta que responde | *¿qué se puede demostrar, y desde qué axiomas?* | *¿qué se puede calcular?* |

Y en último término PeanoRF debe poder servir de **meta-lenguaje** para FOL y ROB++
(§4, con sus límites).

---

## 2. La columna vertebral: la interpretación

Lo que convierte «espejo» de metáfora en teorema es una sola pieza:

```lean
⟦·⟧ : Formula → (Env ℕ₀) → Prop           -- interpretación en el modelo estándar
soundness : axiomsHA ⊢ φ → ∀ env, ⟦φ⟧ env  -- SOLO del fragmento finitario (M-9)
```

Con eso, **cada teorema de PeanoRF baja automáticamente a Peano**. Ésa es la dirección
que el proyecto promete y la que es barata.

Tres observaciones que ordenan el trabajo:

1. **No se puede reutilizar la semántica de FOL.** `FOL.Semantics`/`Soundness` son la
   mitad clásica de FOL y están prohibidas (M-5). Pero **no hacen falta**: interpretar en
   **una** estructura concreta (ℕ₀) no necesita la maquinaria de teoría de modelos
   general, que es clásica por Lindenbaum/Henkin/enumeración. La interpretación de
   PeanoRF se construye desde cero y es constructiva.
2. **La dirección inversa (Peano → PeanoRF) no es automática, y tiene un techo de
   principio.** Lean es mucho más fuerte que HA; por Gödel habrá verdades sobre `ℕ₀`
   demostrables en Lean que HA no demuestra. «Volcar Peano al completo» es una meta
   asintótica, no un teorema.
3. **El espejo hay que GENERARLO, no transcribirlo.** 2193 teoremas a mano se pudren en
   tres meses; es la misma clase de fallo que la documentación que miente. La maquinaria:
   `⌜·⌝` (reflexión de un fragmento de Lean sobre `ℕ₀` a `Formula`), el lema de
   **adecuación** `⟦⌜P⌝⟧ ↔ P`, y una táctica que genere el enunciado objeto.

---

## 3. El eje conceptual: realizabilidad

La división PeanoRF/Peano **es** una interpretación de realizabilidad, y nombrarla así da
el criterio principial de qué va en cada sitio:

> HA tiene la **propiedad de la existencia**: de `⊢ ∃x φ(x)` se extrae un numeral.
> **Los realizadores viven en Peano**, que es computable.

No son dos proyectos espejo: son **las dos mitades de una misma interpretación**.

Dos hechos clásicos blindan la elección constructiva:

- **HA y PA son equiconsistentes** (traducción negativa de Gödel–Gentzen).
- **PA es Π₂-conservativa sobre HA** (A-traducción de Friedman / Dragalin).

Es decir: **la restricción constructiva no cuesta nada** en el contenido aritmético Π₂.
«Puramente constructivo» deja de ser un sacrificio y pasa a ser una elección gratis que,
además, regala los realizadores.

---

## 4. PeanoRF como meta-lenguaje — alcance real y techo

**Lo alcanzable y valioso**: reducir el **compromiso metateórico**. Demostrar que toda la
metateoría que FOL y ROB++ necesitan es formalizable en PeanoRF (fuerza HA/PRA) convierte
a Lean en **vehículo de implementación, no en supuesto matemático**. Está medio construido
aguas arriba: RPP ya tiene `Prf`, `lineWF` y la codificación; lo que le falta es la
inducción para razonar sobre sí mismo — justo lo que PeanoRF aporta.

**Lo que NO es**: PeanoRF «sustituyendo a Lean 4». Lean hace dos trabajos —la lógica
ambiente y la **implementación** (elaborador, kernel, cómputo)— y PeanoRF sólo puede
reemplazar el primero. Algo tiene que **comprobar** las derivaciones, y eso es un
programa. La forma concreta y honesta del objetivo es:

> **Un checker verificado de derivaciones FOL⁼ cuya corrección se demuestra en PeanoRF.**

**El techo, y es duro**: por Gödel II, PeanoRF podrá ser metateoría de FOL⁼ y de Q⁺⁺
—estrictamente más débiles— pero **nunca de sí misma**. La arquitectura es una
**jerarquía, no un círculo**.

---

## 5. Arquitectura

```text
                    ┌──────────────────────────────────────┐
   Peano (ℕ₀) ◄─────┤  ⟦·⟧  interpretación + soundness     │
   computacional    │  (constructiva, sólo fragmento       │
   realizadores     │   finitario — M-9)                   │
                    └──────────────────┬───────────────────┘
                                       │
   ┌───────────────────────────────────┴───────────────────────────┐
   │  PeanoRF.*  — NÚCLEO: HA finitaria                            │
   │  · sólo constructores inductivos de Derives                   │
   │  · inducción EN el conjunto de axiomas, contextos finitos     │
   │  · ⊢ recursivamente enumerable  ⇒  Gödel aplica               │
   └───────────────────────────────────┬───────────────────────────┘
                                       │  (reutiliza donde compensa)
   ┌───────────────────────────────────┴───────────────────────────┐
   │  PeanoRF.Omega.*  — capa ω, declarada y CONTADA               │
   │  · ω-reglas de FOL + meta-axiomas de ROB++                    │
   │  · vale para el espejo; NO para lo fundacional ni el meta-lg. │
   └───────────────────────────────────────────────────────────────┘
                                       │
              FOL⁼ (mitad demostrativa) + ROB++ (Q⁺⁺, Minimal)
```

La frontera la vigila el gate `PeanoRF/Meta/AxiomCheck.lean` en **tres ejes**
(objeto intuicionista · finitario · meta constructivo), probados con smoke tests.
Justificación completa en `DECISIONS.md` **ADR-016**; medición en `sondeos/README.md`.

---

## 6. Roadmap

| Hito | Contenido | Estado |
|---|---|---|
| **H0** | Andamiaje, dependencias, build verde | ✅ 2026-09-06 |
| **H1** | Directiva fundacional + gate de 3 ejes | ✅ 2026-09-06 |
| **H2** | **El conjunto de axiomas de HA**: Q⁺⁺ + esquema de inducción como axiomas, con contextos finitos (M-8). Reprobar finitariamente lo que hoy sale de `ax_induction` | 🔄 infraestructura ✅ + `zero_add` |
| **H3** | **La interpretación `⟦·⟧` en ℕ₀ + soundness del fragmento finitario** (M-9). Aquí aparece el teorema de transferencia: el espejo deja de ser metáfora | ❌ |
| **H4** | **Reflexión `⌜·⌝` + adecuación + táctica**: el espejo se genera, no se transcribe | ❌ |
| **H5** | **Volcado del núcleo aritmético** de Peano (suma, producto, orden, divisibilidad, primos) | ❌ |
| **H6** | **Realizabilidad explícita**: extracción de realizadores hacia Peano | ❌ |
| **H7** | **Metateoría**: formalizar en PeanoRF la sintaxis y el `Prf` de FOL⁼/Q⁺⁺ → checker verificado (§4) | ❌ |

**Orden y por qué**: H2 antes que H3 porque no se puede interpretar lo que no está
axiomatizado; H3 antes que H4 porque la adecuación se enuncia con `⟦·⟧`; H4 antes que H5
porque volcar a mano lo que luego se generará es trabajo tirado.

---

## 7. Riesgos

| Riesgo | Magnitud | Mitigación |
|---|---|---|
| **Reprobar finitariamente lo que ROB++ da por ω** | **Media** (revisado a la baja 2026-09-06 tras H2) | La primera medición real — `zero_add` — dio **coste cero**: misma estructura de prueba, tres axiomas menos. `gen_closed` hace innecesaria la ω-regla sobre contexto cerrado. Falta confirmarlo en el caso **con parámetro** |
| **La parte estructural de Peano** (grupos, Sylow, `FSet`) exige **aritmetizar las estructuras**, no sólo traducir enunciados | Alta | Fuera de H5. `ROB++/Full/Lists` es el punto de partida. No prometer «al completo» |
| Soundness demostrada de más ⇒ inconsistencia latente vía `raa`/`imp_intro` | **Crítica** | M-9 + eje finitario del gate |
| El espejo se desincroniza de Peano | Media | H4: generarlo. Un espejo escrito a mano miente igual que un documento |
| Deuda META heredada de RPP (`Classical.choice` vía codificación `String`) | Baja, con fecha | El autor la sanea aguas arriba → `metaDebtIsError := true` |

---

## 8. Backlog

- [ ] Remoto en GitHub.
- [ ] Activar el control `[B]` de `check-doc-sync.bash` (`SYMBOL_PREFIXES`) cuando existan
      familias de símbolos propias.
- [ ] Abrir el árbol `doc/REFERENCE-{tema}.md` (ADR-007) cuando `REFERENCE.md` deje de
      bastar (~40 módulos).
- [ ] Cerrar la política de axiomas propios para `axiom` de naturaleza distinta a M-8.
- [ ] Convención de nombres que distinga **nivel objeto** de **nivel meta** a simple vista.

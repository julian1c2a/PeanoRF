# TABLERO · el fragmento de Q⁺⁺ con propiedad de disyunción

**Última actualización:** 2026-09-23
**Autor**: Julián Calderón Almendros

> Cuadro de mando de H3ter: **qué axiomas y qué símbolos están dentro del fragmento, cuáles
> no, y por qué**. Es el documento para mirar antes de decidir el siguiente paso.
>
> ⚠️ Todas las cifras de aquí las verifica el **kernel** en
> [`sondeos/audit_fragmento.lean`](../sondeos/audit_fragmento.lean) —`rfl` sobre las
> longitudes de las listas y sobre la pertenencia a cada signatura—. Si una cifra de este
> documento miente, ese sondeo se pone rojo.

---

## 1 · De un vistazo

```lean
qDisjunctionProperty_arithTDCS_final :
    ctxS [] ⊢ᵢ A ∨ B  →  (ctxS [] ⊢ᵢ A) ∨ (ctxS [] ⊢ᵢ B)
```

| | |
|---|---|
| **axiomas dentro** | **26 de los 34** de `coreAxioms` |
| **símbolos dentro** | **10 de los 14** de función, más el predicado `<` |
| **hipótesis** | **ninguna** — `hcon_fragmentS` la descarga con un modelo sobre `ℕ` |
| **footprint** | `[propext, Quot.sound]` |

---

## 2 · Los 34 axiomas

### ✅ Los 26 que están dentro

| axioma | entró con | por qué fue barato |
|---|---|---|
| `ax2` `ax3` `ax4` `ax5` `ax6` `ax7` `ax8` `ax9` `ax10` `ax11` `ax12` `ax18` `ax_L1` `ax_pow_zero` `ax_pow_succ` | A · núcleo | de **Harrop** |
| `ax13_lt_def` | A · núcleo | ⛔ duro — `slash_ax13` |
| `ax19_lt_trichotomy` | A · núcleo | ⛔ duro — `slash_ax19` |
| `ax25_pred_zero` `ax26_pred_succ` | T · `τ` | Harrop, y `τ` se evalúa **sin inducción** |
| `ax16_mod2_succ` `ax24_mod2_of_even` | TM · `%₂` | Harrop |
| `ax21_mod2_range` | TM · `%₂` | ⛔ duro — `slash_ax21`, **y ya estaba barrado** |
| `ax17_div_mod_eq` | TD · `/₂` | Harrop |
| `ax_L0_cons_def` | TDC · `::` | Harrop |
| `ax15_lt_succ_sqrt` | TDCS · `√` | Harrop |
| `ax14_sqrt_le` | TDCS · `√` | ⛔ **duro, y el primero que el fragmento mete sin tenerlo barrado de antes** — `le a b` es `a < b ∨ a = b` |

### ⛔ Los 8 que están fuera, y por qué

| axioma | símbolo | qué lo bloquea | ¿se puede? |
|---|---|---|---|
| `ax29_sub_witness` | `−` | la teoría **calla** fuera de `x ≤ y` | ⛔ **NO, y está MEDIDO**: `sub_neither`, `hNum_false_on_sub` |
| `ax_L2_in_cons` | `∈`, `::` | pide `hIn` — decidir `∈` sobre anclados | ⛔ **NO por inducción** (ADR-046): ver abajo |
| `ax_L3_in_concat` | `∈`, `##` | idem, **y sus dos ramas son `∈`**: no hay nada que refutar bajando a numerales | ⛔ igual |
| `ax_C1_concat_nil` `ax_C2_concat_cons` `ax_C3_concat_assoc` | `##` | recursión sobre lista | ⛔ ver abajo |
| `ax_prodp_nil` `ax_prodp_cons` | `Π_p` | idem | ⛔ ver abajo |

> ⬜⬜ **CONGELADO el 2026-09-23 (ADR-047): la codificación VA A CAMBIAR.** ROB++ tiene
> medido y compilado (`sondeos/CantorSobreyectivo.lean`) que sacando el `σ` fuera
> —`cons a b = σ (pair a b)`— **el Cantor pelado es sobreyectivo y no queda basura**. Si el
> propietario lo adopta, lo de abajo **se cae**: los cinco vuelven a «determinados» y lo que
> había que MEDIR pasa a ser lo que hay que DEMOSTRAR. **No fijar `consNat` hasta entonces.**
>
> ⛔⛔ **RECTIFICADO el 2026-09-22 (ADR-046): NO es que falte inducción sobre listas.**
> Medido en `sondeos/listas_probe.lean`: `nil` es `0` y `cons h t = π(h, t+1)`, luego los
> valores de `cons` son **todos menos `{0, 1, 3, 6, 10, …}`** —los triangulares—. Como `0`
> es `nil`, resulta que **`1`, `3`, `6`, … no son NI `[]` NI `h::t`**: la codificación **no
> es sobreyectiva**, y «todo término es `[]` o un `::`» es **FALSO en el modelo estándar**.
>
> ⇒ no hay nada que demostrar, y un esquema de inducción no lo arreglaría. Lo que toca es
> **medir el negativo**, como con `−`. ⏳ Falta: la relación `MemN` y su variante, y mirar
> `ax_C3` —la asociatividad **sí** dice algo sobre la basura—.
> ⭐ La **inyectividad de Cantor ya no hay que construirla**: es `consN_inj`, en producción
> de ROB++ y medida limpia. ⚠️ Pero **sobre la codificación de HOY** — ver el aviso de
> arriba.

---

## 3 · Los 14 símbolos de función

### ✅ Dentro (10)

`0` · `σ` · `+` · `*` · `^` — el núcleo aritmético
`τ` · `%₂` · `/₂` · `::` · `√` — los cinco que se fueron ganando

### ⛔ Fuera (4)

| símbolo | clase semántica | qué significa |
|---|---|---|
| `−` | **LIBRE** | `ax29` lo condiciona a `x ≤ y` y fuera de ahí **ningún modelo lo fija**. Los modelos deciden, y deciden que no. **Cerrado en negativo.** |
| `##` | ⏳ **probablemente LIBRE** | sus axiomas hablan de `nil` y de `cons`, y **hay códigos que no son ninguna de las dos** (ADR-046) |
| `Π_p` | ⏳ **probablemente LIBRE** | idem |
| `[]` | — | ⚠️ **no aparece nunca en un término**: `nil` es `zero` por definición, y el símbolo `"[]"` es letra muerta |

> 🔑 **La distinción que ADR-037 no hizo, y es la que manda.** Un símbolo puede estar fuera
> por dos razones incompatibles:
> * **libre** — ningún modelo lo fija ⇒ los modelos dan un **negativo** medible (`−`);
> * **determinado en todo modelo** — ⇒ **la técnica de modelos no puede dar un negativo
>   nunca**: o se demuestra, o se deja abierto (`/₂`, `√`, `::`).
>
> ⚠️ **Y `##`/`Π_p` cambiaron de casilla el mismo día** (ADR-046): se daban por
> «determinados, falta inducción», y al medir resultó que **la codificación de listas no es
> sobreyectiva**, así que sobre los códigos que no son listas no los fija nada. Se esperan
> en la primera columna, con `−`.
>
> ADR-037 escribió los cinco iguales. Sólo uno era del primer tipo, y los otros cuatro han
> ido cayendo — y con ADR-046, los de lista apuntan también al primero.

---

## 4 · Los seis escalones

| | signatura | axiomas | teorema | ADR |
|---|---|---|---|---|
| **A** | `LQ` = `0 σ + * ^` | 17 | `qDisjunctionProperty_arith` | 036 |
| **T** | `+ τ` | 19 | `…_arithT` | 037 |
| **TM** | `+ %₂` | 22 | `…_arithTM` | 038 |
| **TD** | `+ /₂` | 23 | `…_arithTD` | 042 |
| **TDC** | `+ ::` | 24 | `…_arithTDC` | 044 |
| **TDCS** | `+ √` | **26** | **`…_arithTDCS_final`** | 045 |

Y en paralelo, el modelo: `natModelK k` sobre `ℕ` interpreta los diez símbolos, verifica
**27** axiomas —los 26 más `ax29_sub_witness`— **para todo `k`**, y de ahí salen las dos
cosas a la vez: `hcon_fragment*` (con `k` fijo) y la medición de `−` (variando `k`).

---

## 5 · Lo que queda

| | qué es | estado |
|---|---|---|
| **`hIn`** | decidir `∈` sobre términos anclados | ⛔ **no se sigue de Q⁺⁺**, y ⚠️ **la razón NO es la que estaba escrita** (ADR-046): no es que falte inducción para probar «todo término es `[]` o un `::`» — esa disyunción es **FALSA**, porque la codificación no es sobreyectiva |
| **`##` y `Π_p`** | los dos que faltan de la signatura | ⏳ **probablemente LIBRES sobre la basura**, como `−`: la medición está acotada y descrita en ADR-046. ⭐ Y **la inyectividad de Cantor que hacía falta YA EXISTE**: `ROBINSON_PlusPlus.Meta.CodeNatInjPrf.consN_inj`, limpia (auditoría del 2026-09-23) |
| **modelo de `coreAxioms` entero** | los 34 en un modelo | ⏳ subiría la medición de `−` de 27 axiomas a 34, y haría **medible** la no-derivabilidad de las ramas de `junk_probe`. ⚠️ **RPP tiene 25 de los 34 en `sondeos/ModeloNat.lean`, con la MISMA maquinaria** — antes de seguir, hablarlo con ellos |
| **no-derivabilidad de `junk_probe`** | la otra mitad del contraejemplo de H3ter | ⏳ hoy es **argumento por solidez**, no medición. La herramienta ya está: un modelo parametrizado por la interpretación de `foo`/`bar` |
| **el encargo a FOL** | `Calculus/Subst.lean` y `fdepth` duplicados | ✅ **CONTESTADO** (ADR-047, [respuesta](RESPUESTA-FOL-2026-09-23.md)). **§3 ACEPTADO**: `formulaComplexity` y `complexity_substFormula` bajan a un módulo base ⇒ planificar la **retirada de `fdepth`** cuando esté. ⬜ **§2 (sustitución paralela): decisión del propietario** — FOL congeló el 2026-09-23 y nuestra recomendación fue **que NO entrara** |
| **divergencia de polimorfismo** | FOL generiza en `Sym`, PeanoRF sigue monomórfico | ⚠️ hoy gratis por los `abbrev`; el riesgo es el paso que no lleve uno |

> ⬜⬜ **Dos de estas filas dependen de una decisión que no es nuestra** (ADR-047): si ROB++
> adopta `cons a b = σ (pair a b)`, la codificación pasa a ser **sobreyectiva** y ADR-046 se
> cae — `hIn`, `##` y `Π_p` vuelven de «probablemente libres» a **«determinados»**, y con
> ellos `consN_inj` deja de ser sobre la codificación de hoy. **Parado hasta entonces.**

---

## 6 · Cómo comprobarlo sin creerme

```bash
lake env lean sondeos/audit_fragmento.lean    # las cifras y las signaturas, por rfl
lake build                                     # el gate de los tres ejes
bash check-doc-sync.bash                       # [A]…[E], [H]
bash check-coherencia.bash                     # [F], [G]
```

⚠️ Y la comprobación que este proyecto tiene escrita con sangre: **antes de tocar nada,
re-medir aguas arriba**. FOL y ROB++ se mueven varias veces al día.

---

⬆️ **[Índice de referencia](../REFERENCE.md)** · 🎯 **[Nodo HA](REFERENCE-HA.md)** ·
📋 **[Próximos pasos](../NEXT-STEPS.md)**

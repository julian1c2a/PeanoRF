# TABLERO · el fragmento de Q⁺⁺ con propiedad de disyunción

**Última actualización:** 2026-09-22
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
| `ax_L2_in_cons` | `∈`, `::` | pide `hIn` — decidir `∈` sobre anclados | ⏳ pide inducción sobre listas |
| `ax_L3_in_concat` | `∈`, `##` | idem, **y sus dos ramas son `∈`**: no hay nada que refutar bajando a numerales | ⏳ igual |
| `ax_C1_concat_nil` `ax_C2_concat_cons` `ax_C3_concat_assoc` | `##` | recursión sobre lista: hay que saber si un numeral es `nil` o `cons` | ⏳ |
| `ax_prodp_nil` `ax_prodp_cons` | `Π_p` | idem | ⏳ |

---

## 3 · Los 14 símbolos de función

### ✅ Dentro (10)

`0` · `σ` · `+` · `*` · `^` — el núcleo aritmético
`τ` · `%₂` · `/₂` · `::` · `√` — los cinco que se fueron ganando

### ⛔ Fuera (4)

| símbolo | clase semántica | qué significa |
|---|---|---|
| `−` | **LIBRE** | `ax29` lo condiciona a `x ≤ y` y fuera de ahí **ningún modelo lo fija**. Los modelos deciden, y deciden que no. **Cerrado en negativo.** |
| `##` | determinado | recursión sobre lista |
| `Π_p` | determinado | recursión sobre lista |
| `[]` | — | ⚠️ **no aparece nunca en un término**: `nil` es `zero` por definición, y el símbolo `"[]"` es letra muerta |

> 🔑 **La distinción que ADR-037 no hizo, y es la que manda.** Un símbolo puede estar fuera
> por dos razones incompatibles:
> * **libre** — ningún modelo lo fija ⇒ los modelos dan un **negativo** medible (`−`);
> * **determinado en todo modelo** — ⇒ **la técnica de modelos no puede dar un negativo
>   nunca**: o se demuestra, o se deja abierto (`/₂`, `√`, `::`, y presumiblemente `##`,
>   `Π_p`).
>
> ADR-037 escribió los cinco iguales. Sólo uno era del primer tipo, y los otros cuatro han
> ido cayendo.

---

## 4 · Los seis escalones

| | signatura | axiomas | teorema | ADR |
|---|---|---|---|---|
| **A** | `LQ` = `0 σ + * ^` | 17 | `qDisjunctionProperty_arith` | 036 |
| **T** | `+ τ` | 19 | `…_arithT` | 037 |
| **TM** | `+ %₂` | 22 | `…_arithTM` | 038 |
| **TD** | `+ /₂` | 23 | `…_arithTD` | 042 |
| **TDC** | `+ ::` | 24 | `…_arithTDC` | 044 |
| **TDCS** | `+ √` | **26** | **`…_arithTDCS_final`** | *(este paso)* |

Y en paralelo, el modelo: `natModelK k` sobre `ℕ` interpreta los diez símbolos, verifica
**27** axiomas —los 26 más `ax29_sub_witness`— **para todo `k`**, y de ahí salen las dos
cosas a la vez: `hcon_fragment*` (con `k` fijo) y la medición de `−` (variando `k`).

---

## 5 · Lo que queda

| | qué es | estado |
|---|---|---|
| **`hIn`** | decidir `∈` sobre términos anclados | ⛔ **no se sigue de Q⁺⁺**: haría falta que la teoría probara que todo término es `[]` o un `::`, y eso es inducción sobre listas, que `coreAxioms` no tiene. Es lo que bloquea `ax_L2` y `ax_L3` |
| **`##` y `Π_p`** | los dos que faltan de la signatura | ⏳ piden lo mismo que `hIn`: distinguir `nil` de `cons` sobre un numeral |
| **modelo de `coreAxioms` entero** | los 34 en un modelo | ⏳ subiría la medición de `−` de 27 axiomas a 34, y haría **medible** la no-derivabilidad de las ramas de `junk_probe` |
| **no-derivabilidad de `junk_probe`** | la otra mitad del contraejemplo de H3ter | ⏳ hoy es **argumento por solidez**, no medición. La herramienta ya está: un modelo parametrizado por la interpretación de `foo`/`bar` |
| **el encargo a FOL** | `Calculus/Subst.lean` y `fdepth` duplicados | ⏳ sin contestar |
| **divergencia de polimorfismo** | FOL generiza en `Sym`, PeanoRF sigue monomórfico | ⚠️ hoy gratis por los `abbrev`; el riesgo es el paso que no lleve uno |

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

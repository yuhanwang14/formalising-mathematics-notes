# Lean Syntax & Proof Logic Cheatsheet (Coursework 2)

Quick reference for every Lean construct used in `Coursework2.lean`.

---

## 1. File Structure

| Syntax | Meaning |
|---|---|
| `import Mathlib.X.Y.Z` | Load a Mathlib module; makes its definitions, lemmas, and instances available. |
| `open scoped MeasureTheory ENNReal NNReal` | Bring scoped notations (e.g. `≪`, `⟂ₘ`, `ℝ≥0∞`) into scope without opening the full namespace. |
| `open Set Filter MeasureTheory` | Open namespaces so you can write `range` instead of `Set.range`, etc. |
| `namespace Project` / `end Project` | All definitions/theorems inside live under the `Project` prefix, avoiding name clashes with Mathlib. |
| `section X` / `end X` | Group related declarations. `variable` declarations inside a section are auto-inserted into any theorem that uses them, and discarded when the section ends. |

## 2. Variables & Universe Polymorphism

| Syntax | Meaning |
|---|---|
| `variable {α : Type*}` | Declare an implicit type variable. `Type*` means "any universe level"—Lean infers it. Curly braces `{}` make it implicit (Lean fills it in from context). |
| `[MeasurableSpace α]` | A **type class instance**: tells Lean that `α` carries a σ-algebra. Square brackets `[]` mean Lean finds the instance automatically via instance resolution. |
| `[SigmaFinite μ]` | Another type class: asserts μ is σ-finite. Lean uses this to auto-synthesise `HaveLebesgueDecomposition` instances. |
| `variable {μ ν : Measure α}` | Implicit measure variables. Any theorem in the section that mentions `μ` or `ν` automatically receives these as implicit arguments. |

## 3. Definitions

| Syntax | What it does |
|---|---|
| `noncomputable def positivePart (s : SignedMeasure α) : Measure α := ...` | Define a function. `noncomputable` is required because the Jordan decomposition involves classical choice (not constructively computable). |
| `instance (s : SignedMeasure α) : IsFiniteMeasure (positivePart s) := ...` | Register a **type class instance**: tells Lean that `positivePart s` is always a finite measure, so downstream lemmas requiring `[IsFiniteMeasure ...]` can use it. |

## 4. Theorem/Lemma Declarations

```
theorem name (hyp₁ : Type₁) (hyp₂ : Type₂) : Goal := proof
```

- `theorem` and `lemma` are interchangeable; both produce proof terms.
- Named hypotheses in parentheses `()` are explicit; in curly braces `{}` they're implicit.
- After the colon is the **type** (= the statement to prove).
- After `:=` is the **proof term**, or `by` starts **tactic mode**.

## 5. Tactics (used in `by` blocks)

### Introducing & Destructuring

| Tactic | What it does | Example in code |
|---|---|---|
| `intro hac` | Introduce a hypothesis from a `∀` or `→` goal. | `intro s hs` introduces a set and its measurability. |
| `rcases h with ⟨a, b, c, d⟩` | Destructure an existential or structure into named components. Uses angle brackets `⟨⟩`. | `rcases hms with ⟨A, hA_meas, hνA, hμAc⟩` unpacks the 4 fields of `MutuallySingular`. |
| `obtain ⟨j, hj_meas, hji, hj_neg, hj_val⟩ := expr` | Like `rcases` but takes the proof term on the right of `:=`. | Used in Hahn decomposition to unpack an existential. |
| `rintro ⟨f, _, hf_eq⟩` | Combines `intro` + `rcases` in one step. The `_` discards a component. | Used in the `⇐` direction to introduce and destructure the existential witness. |

### Rewriting

| Tactic | What it does | Example in code |
|---|---|---|
| `rw [lemma]` | Rewrite the goal using `lemma` (left-to-right). | `rw [inter_union_compl]` replaces `(s ∩ A) ∪ (s ∩ Aᶜ)` with `s`. |
| `rw [← lemma]` | Rewrite right-to-left. | `rw [← hsplit]` replaces `s` with `(s ∩ A) ∪ (s ∩ Aᶜ)`. |
| `rw [hzero]` | Rewrite using a local hypothesis. | Substitutes `ν.singularPart μ = 0` into the goal. |
| `unfold name` | Unfold a definition in the goal. | `unfold positivePart negativePart` expands to `toJordanDecomposition.posPart`. |

### Finishing

| Tactic | What it does | Example in code |
|---|---|---|
| `exact term` | Provide the exact proof term for the goal. | `exact s.toSignedMeasure_toJordanDecomposition.symm` |
| `congr 1` | Reduce `f a = f b` to `a = b` (congruence). The `1` means "peel one layer". | Used to split `0 + 0 = ...` into two separate goals for each summand. |

### Existential Witnesses

| Tactic | What it does | Example in code |
|---|---|---|
| `use term` | Provide a witness for an `∃` goal. | `use ν.rnDeriv μ` witnesses the density function. |
| `constructor` | Split a `∧` (and) or `↔` (iff) goal into two subgoals. | Used to split `Measurable f ∧ ν = μ.withDensity f`. |

### Extensionality

| Tactic | What it does | Example in code |
|---|---|---|
| `ext s hs` | Apply extensionality. For measures: reduces `ν = 0` to `ν s = 0` for arbitrary measurable `s`, binding both the set `s` and its measurability proof `hs`. | Used in `eq_zero_of_ac_of_mutuallySingular`. |

### Calc Blocks

```lean
calc a = b := proof₁
  _ = c := proof₂
  _ = d := proof₃
```

A **calc block** chains equalities (or inequalities like `≤`). Each `_` refers to the right-hand side of the previous line. You can mix `=` and `≤` as long as they compose transitively. Used twice in this file:
- In the key lemma to chain `ν s = ν(s∩A ∪ s∩Aᶜ) = ν(s∩A) + ν(s∩Aᶜ) = 0 + 0 = 0`.
- In the forward direction of Radon-Nikodym to chain `ν = νₛ + f·μ = 0 + f·μ = f·μ`.

### Local Hypotheses

| Tactic | What it does |
|---|---|
| `have h : T := proof` | Introduce a local hypothesis `h` of type `T`. |
| `have h := expr` | Lean infers the type from `expr`. |

## 6. Proof Terms (used without `by`)

Many theorems are proved by a single **term** rather than tactics:

| Pattern | Meaning | Example |
|---|---|---|
| `Iff.rfl` | The two sides of `↔` are definitionally equal. | `ac_def` — `ν ≪ μ` literally *is* `∀ s, μ s = 0 → ν s = 0`. |
| `⟨proof₁, proof₂⟩` | Anonymous constructor for a structure or `∧`. | `⟨Measure.MutuallySingular.symm, Measure.MutuallySingular.symm⟩` builds an `↔`. |
| `expr.symm` | Flip an equality `a = b` to `b = a`. | `s.toSignedMeasure_toJordanDecomposition.symm` |
| `expr.trans expr2` | Chain `a = b` and `b = c` into `a = c`. Also works for `≪` (absolute continuity is transitive). | `hνμ.trans hμρ` |
| `.mp` | Extract the forward direction of an `↔`. | `(withDensity_eq_iff_of_sigmaFinite ...).mp hf_eq` |

## 7. Key Types & Notations

| Lean notation | Mathematical meaning | Lean type |
|---|---|---|
| `ℝ≥0∞` | Extended non-negative reals $[0,\infty]$ | `ENNReal` |
| `Measure α` | A measure on `α` (values in `ℝ≥0∞`) | `MeasureTheory.Measure α` |
| `SignedMeasure α` | A signed measure (values in `ℝ`) | `MeasureTheory.SignedMeasure α` |
| `ν ≪ μ` | Absolute continuity: `∀ s, μ s = 0 → ν s = 0` | `Measure.AbsolutelyContinuous ν μ` |
| `ν ⟂ₘ μ` | Mutual singularity: `∃ A, MeasurableSet A ∧ ν A = 0 ∧ μ Aᶜ = 0` | `Measure.MutuallySingular ν μ` |
| `μ.withDensity f` | The measure $A \mapsto \int_A f\,d\mu$ | `Measure.withDensity μ f` |
| `ν.rnDeriv μ` | Radon-Nikodym derivative $d\nu/d\mu$ | `Measure.rnDeriv ν μ` |
| `ν.singularPart μ` | Singular part $\nu_s$ in Lebesgue decomposition | `Measure.singularPart ν μ` |
| `f =ᵐ[μ] g` | Equal μ-almost everywhere | `Filter.EventuallyEq (Measure.ae μ) f g` |
| `0 ≤[P] s` | `P` is a positive set for signed measure `s` | `SignedMeasure.restrict 0 P ≤ SignedMeasure.restrict s P` |
| `MeasurableSet P` | `P` belongs to the σ-algebra | type class predicate |
| `Set.Aᶜ` | Complement of set `A` | `Set.compl A` |

## 8. Named Arguments

```lean
have hdecomp := lebesgue_decomposition (μ := μ) (ν := ν)
```

The `(μ := μ)` syntax provides **named implicit arguments** explicitly. This is needed when Lean cannot infer which measure is `μ` and which is `ν` from the goal alone.

## 9. Pipe Operator

```lean
measure_mono inter_subset_right |>.trans (le_of_eq hνA)
```

`|>` pipes the result of the left side into a dot-method on the right. Equivalent to:
```lean
(measure_mono inter_subset_right).trans (le_of_eq hνA)
```

## 10. The `·` (focused) Syntax

Inside a tactic block, `·` focuses on a single subgoal:
```lean
congr 1
· exact le_antisymm ...   -- first subgoal
· have hμ := ...           -- second subgoal
```

Each `·` block solves one goal. Indentation determines scope.

## 11. ENNReal Proof Patterns

Measures take values in `ℝ≥0∞`, where subtraction is truncated. Two recurring patterns:

**Showing `x = 0` from an upper bound:**
```lean
le_antisymm (bound_showing_x_le_0) (zero_le _)
```
`zero_le _` provides `0 ≤ x` for free (everything in `ℝ≥0∞` is ≥ 0).

**Chaining inequality to equality for absolute continuity:**
```lean
have hμ : μ (s ∩ Aᶜ) ≤ μ Aᶜ := measure_mono inter_subset_right
exact hac (hμ.trans (le_of_eq hμAc) |>.antisymm (zero_le _))
```
1. `measure_mono` gives the inequality `μ(s ∩ Aᶜ) ≤ μ(Aᶜ)`.
2. `.trans (le_of_eq hμAc)` chains it with `μ(Aᶜ) = 0` to get `μ(s ∩ Aᶜ) ≤ 0`.
3. `.antisymm (zero_le _)` closes to `μ(s ∩ Aᶜ) = 0`.
4. `hac` (absolute continuity) then gives `ν(s ∩ Aᶜ) = 0`.

## 12. Key Mathlib Lemmas Used

| Lemma | Statement (informal) |
|---|---|
| `SignedMeasure.exists_compl_positive_negative` | Hahn decomposition exists. |
| `SignedMeasure.exists_subset_restrict_nonpos` | Negative-measure set contains a negative subset. |
| `s.toSignedMeasure_toJordanDecomposition` | Jordan decomposition identity `s = s⁺ - s⁻`. |
| `s.toJordanDecomposition.mutuallySingular` | `s⁺ ⟂ₘ s⁻`. |
| `withDensity_absolutelyContinuous μ f` | `μ.withDensity f ≪ μ` (density is always AC). |
| `ν.haveLebesgueDecomposition_add μ` | `ν = ν.singularPart μ + μ.withDensity (ν.rnDeriv μ)`. |
| `ν.mutuallySingular_singularPart μ` | `ν.singularPart μ ⟂ₘ μ`. |
| `Measure.measurable_rnDeriv ν μ` | The RN derivative is measurable. |
| `Measure.withDensity_rnDeriv_eq ν μ hac` | If `ν ≪ μ`, then `μ.withDensity (ν.rnDeriv μ) = ν`. |
| `withDensity_eq_iff_of_sigmaFinite` | Two densities give the same measure iff they're a.e. equal. |
| `Measure.rnDeriv_mul_rnDeriv` | Chain rule for RN derivatives. |
| `Measure.rnDeriv_self ν` | `dν/dν = 1` a.e. |
| `measure_union hdisj hs` | `μ(s ∪ t) = μ s + μ t` when disjoint and `t` is measurable. |
| `measure_mono h` | `s ⊆ t → μ s ≤ μ t`. |
| `Measure.add_apply` | `(μ + ν) s = μ s + ν s`. |
| `le_add_of_nonneg_right` | `0 ≤ b → a ≤ a + b`. |
| `le_antisymm` | `a ≤ b → b ≤ a → a = b`. |
| `le_of_eq` | `a = b → a ≤ b`. |
| `zero_le _` | `0 ≤ x` in `ℝ≥0∞`. |
| `zero_add _` | `0 + x = x`. |
| `add_zero _` | `x + 0 = x`. |
| `inter_union_compl` | `(s ∩ A) ∪ (s ∩ Aᶜ) = s`. |
| `inter_subset_right` | `s ∩ A ⊆ A`. |

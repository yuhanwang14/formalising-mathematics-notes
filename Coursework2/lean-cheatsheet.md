# Oral Exam Cheatsheet — Coursework 2

Study guide organized by **what you'll be asked**, not by Lean syntax category.

---

## The Big Picture

You formalized: **Hahn → Jordan → Lebesgue → Radon-Nikodym**.

- Parts 1, 2, 4, 6: thin wrappers around Mathlib (1-2 line proofs)
- Part 3: key lemma `eq_zero_of_ac_of_mutuallySingular` — **your main original proof**
- Part 5: `radon_nikodym` — **the main theorem, uses Part 3**

---

## Quick Tactic Reference

| Tactic | One-line explanation |
|---|---|
| `intro h` | Assume the hypothesis (for `→` or `∀`) |
| `rcases h with ⟨a, b, c⟩` | Unpack a structure/existential into named parts |
| `obtain ⟨a, b⟩ := expr` | Same as rcases but from an expression |
| `rintro ⟨a, _, b⟩` | `intro` + `rcases` in one step; `_` discards |
| `exact term` | "This is the proof" — supply the exact term |
| `use witness` | Provide the witness for an `∃` goal |
| `constructor` | Split `∧` or `↔` into two subgoals |
| `rw [lemma]` / `rw [← lemma]` | Rewrite goal left-to-right / right-to-left |
| `unfold name` | Expand a definition so Lean can see through it |
| `ext s hs` | Measure extensionality: prove equal on every measurable set |
| `congr 1` | "Both sides have same outer function, prove args equal" |
| `have h := ...` | Introduce a local fact |
| `calc` | Chain equalities/inequalities step by step |
| `· ...` | Focus on one subgoal (after `constructor`, `congr`, etc.) |

---

## Part-by-Part: What to Say

### Part 1 — Hahn Decomposition

**Q: What does `hahn_decomposition_exists` do?**
> It says: for any signed measure s, there's a measurable set P where s is non-negative on P and non-positive on Pᶜ. The proof is a single call to `SignedMeasure.exists_compl_positive_negative`.

**Q: What does `exists_negative_subset_of_negative_measure` do?**
> If s(i) < 0, there's a subset j ⊆ i that is a negative set with s(j) < 0. The Mathlib lemma returns fields in a different order than my statement, so I use `obtain` to unpack and `exact ⟨...⟩` to repack in the right order.

**Q: What does `0 ≤[P] s` mean?**
> The restriction of s to P is non-negative: for every measurable B ⊆ P, s(B) ≥ 0.

### Part 2 — Jordan Decomposition

**Q: Why `noncomputable`?**
> The Jordan decomposition uses classical choice (Hahn decomposition is non-constructive), so Lean marks it noncomputable.

**Q: What do the `instance` declarations do?**
> They register `IsFiniteMeasure` with Lean's type class system, so any downstream lemma that needs `[IsFiniteMeasure ...]` can find it automatically.

**Q: Why `unfold` before `exact`?**
> I defined `positivePart s` as a wrapper around `s.toJordanDecomposition.posPart`. Lean doesn't automatically see through my wrapper, so `unfold` expands it. Then the goal matches the Mathlib lemma and `exact` works.

**Q: What does `.symm` do?**
> Flips an equality. Mathlib gives `s⁺ - s⁻ = s`, but I need `s = s⁺ - s⁻`.

### Part 3 — Key Lemma (the one you'll be grilled on)

**Statement**: If ν ≪ μ and ν ⟂ₘ μ, then ν = 0.

**Line-by-line**:

1. `rcases hms with ⟨A, hA_meas, hνA, hμAc⟩`
   — Unpack mutual singularity: get separating set A, its measurability, ν(A)=0, μ(Aᶜ)=0.

2. `ext s hs`
   — Reduce "ν = 0" to "ν(s) = 0 for every measurable s". Binds s and hs.

3. `have hsplit` / `have hdisj`
   — s = (s∩A) ∪ (s∩Aᶜ) and the two pieces are disjoint. The disjointness proof destructures a point x in both pieces and derives a contradiction (x ∈ Aᶜ but x ∈ A).

4. `calc ν s = ν((s∩A) ∪ (s∩Aᶜ))` — just rewrite using hsplit.

5. `_ = ν(s∩A) + ν(s∩Aᶜ)` — apply `measure_union`, which needs: (a) `hdisj : Disjoint`, (b) `hs.inter hA_meas.compl : MeasurableSet (s ∩ Aᶜ)`.

6. `_ = 0 + 0` — `congr 1` splits into two subgoals:
   - **First**: ν(s∩A) = 0. By monotonicity ν(s∩A) ≤ ν(A) = 0, then `le_antisymm ... (zero_le _)`.
   - **Second**: ν(s∩Aᶜ) = 0. By monotonicity μ(s∩Aᶜ) ≤ μ(Aᶜ) = 0, chain to μ(s∩Aᶜ) = 0, then apply hac.

7. `_ = 0` — `add_zero 0`.

**Q: Why `le_antisymm` instead of just saying "≤ 0 means = 0"?**
> Measures are in ℝ≥0∞ (ENNReal). There's no subtraction or negation. To get x = 0 you need x ≤ 0 AND 0 ≤ x. `zero_le _` gives the second part for free.

**Q: What does `|>` do?**
> Pipe operator. `expr |>.method(args)` is `(expr).method(args)`. Just a style choice.

### Part 4 — Lebesgue Decomposition

**Q: Why are there explicit arguments `(μ ν : Measure α)` in `singularPart_mutuallySingular'`?**
> Both μ and ν have the same type `Measure α`, so Lean can't tell which is which from context. Making them explicit disambiguates.

**Q: How does `HaveLebesgueDecomposition` work?**
> It's a type class. When you declare `[SigmaFinite μ] [SigmaFinite ν]` in the section, Lean's instance resolution automatically finds a `HaveLebesgueDecomposition ν μ` instance, which is what `haveLebesgueDecomposition_add` needs. You don't construct it explicitly.

### Part 5 — Radon-Nikodym (second proof you'll be grilled on)

**Structure**:
```
constructor               -- split ↔ into ⇒ and ⇐
· intro hac               -- ⇒ direction: assume ν ≪ μ
  use ν.rnDeriv μ         -- witness: the RN derivative
  constructor             -- split ∧: measurability + identity
  · exact ...             -- measurability: library lemma
  · ...                   -- identity: the hard part
    [show νₛ ≪ μ]        -- via inner calc: νₛ(s) ≤ ν(s) = 0
    [apply key lemma]     -- νₛ ≪ μ + νₛ ⟂ μ ⟹ νₛ = 0
    [final calc]          -- ν = νₛ + f·μ = 0 + f·μ = f·μ
· rintro ⟨f, _, hf_eq⟩   -- ⇐ direction: given density, show AC
  rw [hf_eq]
  exact withDensity_absolutelyContinuous μ f
```

**Q: Why `(μ := μ) (ν := ν)` in the `have` statements?**
> Named arguments. Both μ and ν are `Measure α` in the section, so Lean can't infer which is which. The `(μ := μ)` syntax forces the assignment.

**Q: How does the inner calc show νₛ(s) ≤ ν(s)?**
> Three steps:
> 1. `le_add_of_nonneg_right (zero_le _)`: νₛ(s) ≤ νₛ(s) + withDensity(s) (adding non-negative)
> 2. `(Measure.add_apply _ _ _).symm`: rewrite as (νₛ + withDensity)(s)
> 3. `rw [← hdecomp]`: replace νₛ + withDensity with ν (Lebesgue decomposition)

**Q: What does `rintro ⟨f, _, hf_eq⟩` do?**
> Introduces the existential witness: f is the density, `_` discards the measurability proof (not needed), hf_eq is the identity ν = μ.withDensity f.

### Part 6 — Applications

**Q: What does `=ᵐ[ρ]` mean?**
> Almost everywhere equality: f and g differ only on a set of ρ-measure zero. Full type: `Filter.EventuallyEq (Measure.ae ρ)`.

**Q: Why three `[SigmaFinite]` instances?**
> Chain rule involves μ, ν, ρ — all three need to be σ-finite for the Mathlib lemma to apply.

---

## Key ENNReal Pattern (appears 3× in the file)

To show `x = 0` in ℝ≥0∞:
```
le_antisymm (proof_that_x_≤_0) (zero_le _)
```
- You can't just say x ≤ 0 ⟹ x = 0 (that's a real-number fact).
- In ℝ≥0∞ you need both directions: `x ≤ 0` and `0 ≤ x`.
- `zero_le _` is always true in ℝ≥0∞.

To convert an inequality to equality for absolute continuity:
```
measure_mono inter_subset_right        -- μ(s ∩ Aᶜ) ≤ μ(Aᶜ)
  |>.trans (le_of_eq hμAc)            -- ... ≤ 0
  |>.antisymm (zero_le _)             -- ... = 0
```
Then `hac` (absolute continuity) turns μ(...) = 0 into ν(...) = 0.

---

## Likely Exam Questions (Top 5)

1. **"Walk me through `eq_zero_of_ac_of_mutuallySingular` line by line."**
2. **"How do you show νₛ ≪ μ in the forward direction of `radon_nikodym`?"**
3. **"Why do you need `le_antisymm` / what is ENNReal?"**
4. **"Why `unfold` in Part 2?" / "Why `(μ := μ)` in Part 5?"**
5. **"What does the key lemma say mathematically and why does it matter?"**
   → If ν ≪ μ and ν ⟂ μ then ν = 0. It kills the singular part in the R-N proof.

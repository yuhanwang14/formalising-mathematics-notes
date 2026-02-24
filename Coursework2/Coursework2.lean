/-
Copyright (c) 2026 Yuhan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhan Wang
-/
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The Radon-Nikodym Theorem

This file develops the theory leading to the Radon-Nikodym theorem, which characterizes
when a measure ν is absolutely continuous with respect to another measure μ in terms of
the existence of a density function (the Radon-Nikodym derivative).

## Overview

The Radon-Nikodym theorem is one of the most important results in measure theory,
with applications in probability (conditional expectation), statistics (likelihood ratios),
and functional analysis. The path to proving it involves several key intermediate results:

1. **Hahn Decomposition**: Every signed measure admits a decomposition into positive/negative parts
2. **Jordan Decomposition**: s = s⁺ - s⁻ for mutually singular measures s⁺, s⁻
3. **Lebesgue Decomposition**: ν = νₛ + νₐc where νₛ ⟂ μ and νₐc ≪ μ
4. **Radon-Nikodym**: ν ≪ μ ↔ ∃ f, ν = f • μ

## Main Results

### Part 1: Signed Measures and Hahn Decomposition
- `hahn_decomposition_exists`: The Hahn decomposition theorem

### Part 2: Jordan Decomposition
- `jordan_decomposition_eq`: s = s⁺ - s⁻
- `jordan_parts_mutuallySingular`: s⁺ ⟂ₘ s⁻

### Part 3: Absolute Continuity and Mutual Singularity
- `eq_zero_of_ac_of_mutuallySingular`: ν ≪ μ ∧ ν ⟂ μ → ν = 0

### Part 4: Lebesgue Decomposition
- `lebesgue_decomposition`: ν = νₛ + (dν/dμ) • μ

### Part 5: Radon-Nikodym Theorem
- `radon_nikodym`: ν ≪ μ ↔ ∃ f, ν = f • μ (σ-finite case)

## References

* P.F. Rodriguez, *MATH50006 Measure and Integration Lecture Notes*, Chapter 4
* W. Rudin, *Real and Complex Analysis*, Chapter 6
* P.R. Halmos, *Measure Theory*, Chapter VI
-/

open scoped MeasureTheory ENNReal NNReal
open Set Filter MeasureTheory

namespace Project

variable {α : Type*} [MeasurableSpace α]

/-! ## Part 1: Signed Measures and the Hahn Decomposition

A signed measure is a σ-additive function s : Σ → ℝ (where Σ is a σ-algebra).
Unlike positive measures, signed measures can take negative values.

The Hahn decomposition theorem states that for any signed measure s, the measurable
space can be partitioned into a positive set P and a negative set N = Pᶜ.

Key definitions from Mathlib:
- `SignedMeasure α` is the type of signed measures on α
- `s ≤[i] 0` means i is a negative set (s(B) ≤ 0 for all B ⊆ i)
- `0 ≤[i] s` means i is a positive set (s(B) ≥ 0 for all B ⊆ i)
-/

section HahnDecomposition

variable {s : SignedMeasure α}

/-- The Hahn Decomposition Theorem: Every signed measure admits a decomposition
X = P ∪ N where P is positive and N is negative.

Proof strategy (from lecture notes Theorem 4.13):
1. Let b = inf{s(B) : B is a negative set}
2. Find negative sets Bₙ with s(Bₙ) → b
3. Show B = ⋃ Bₙ is negative with s(B) = b > -∞
4. Show A = Bᶜ is positive (else we could find a "more negative" set)
-/
theorem hahn_decomposition_exists :
    ∃ (P : Set α), MeasurableSet P ∧ 0 ≤[P] s ∧ s ≤[Pᶜ] 0 := by
  -- Use Mathlib's exists_compl_positive_negative
  exact SignedMeasure.exists_compl_positive_negative s

/-- A set of negative measure contains a negative subset (Lemma 4.16). -/
theorem exists_negative_subset_of_negative_measure {i : Set α} (hi_neg : s i < 0) :
    ∃ j ⊆ i, MeasurableSet j ∧ s ≤[j] 0 ∧ s j < 0 := by
  obtain ⟨j, hj_meas, hji, hj_neg, hj_val⟩ := SignedMeasure.exists_subset_restrict_nonpos hi_neg
  exact ⟨j, hji, hj_meas, hj_neg, hj_val⟩

end HahnDecomposition

/-! ## Part 2: The Jordan Decomposition

The Jordan decomposition theorem states that every signed measure s can be uniquely
written as s = s⁺ - s⁻ where s⁺ and s⁻ are mutually singular positive measures.

The positive and negative parts are defined using the Hahn decomposition:
- s⁺(A) = s(A ∩ P) where P is the positive set
- s⁻(A) = -s(A ∩ N) where N = Pᶜ is the negative set

This is Theorem 4.19 in the lecture notes.
-/

section JordanDecomposition

variable {s : SignedMeasure α}

/-- The positive part of the Jordan decomposition. -/
noncomputable def positivePart (s : SignedMeasure α) : Measure α :=
  s.toJordanDecomposition.posPart

/-- The negative part of the Jordan decomposition. -/
noncomputable def negativePart (s : SignedMeasure α) : Measure α :=
  s.toJordanDecomposition.negPart

/-- Instance: the positive part is a finite measure. -/
instance (s : SignedMeasure α) : IsFiniteMeasure (positivePart s) :=
  s.toJordanDecomposition.posPart_finite

/-- Instance: the negative part is a finite measure. -/
instance (s : SignedMeasure α) : IsFiniteMeasure (negativePart s) :=
  s.toJordanDecomposition.negPart_finite

/-- The Jordan Decomposition: s = s⁺ - s⁻.
This is Theorem 4.19 in the lecture notes. -/
theorem jordan_decomposition_eq :
    s = (positivePart s).toSignedMeasure - (negativePart s).toSignedMeasure := by
  unfold positivePart negativePart
  exact s.toSignedMeasure_toJordanDecomposition.symm

/-- The positive and negative parts are mutually singular. -/
theorem jordan_parts_mutuallySingular :
    positivePart s ⟂ₘ negativePart s := by
  unfold positivePart negativePart
  exact s.toJordanDecomposition.mutuallySingular

/-- The total variation measure |s| = s⁺ + s⁻. -/
noncomputable def totalVariation (s : SignedMeasure α) : Measure α :=
  positivePart s + negativePart s

end JordanDecomposition

/-! ## Part 3: Absolute Continuity and Mutual Singularity

Two fundamental relations between measures:
- **Absolute continuity** (ν ≪ μ): μ(A) = 0 ⟹ ν(A) = 0
- **Mutual singularity** (ν ⟂ μ): ∃ A, μ(A) = 0 ∧ ν(Aᶜ) = 0

These concepts are "opposite" in a sense: if ν ≪ μ and ν ⟂ μ, then ν = 0.
-/

section AbsolutelyContinuous

variable {μ ν : Measure α}

/-- Absolute continuity: ν ≪ μ means every μ-null set is ν-null. -/
lemma ac_def : ν ≪ μ ↔ ∀ s, μ s = 0 → ν s = 0 :=
  Iff.rfl

/-- If ν = f • μ (ν has density f w.r.t. μ), then ν ≪ μ.
This is the easy direction of Radon-Nikodym. -/
theorem absolutelyContinuous_withDensity (f : α → ℝ≥0∞) :
    μ.withDensity f ≪ μ :=
  withDensity_absolutelyContinuous μ f

/-- Mutual singularity is symmetric. -/
theorem mutuallySingular_symm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ :=
  ⟨Measure.MutuallySingular.symm, Measure.MutuallySingular.symm⟩

/-- Key lemma: If ν ≪ μ and ν ⟂ μ, then ν = 0.
This is crucial for the Radon-Nikodym theorem. -/
theorem eq_zero_of_ac_of_mutuallySingular (hac : ν ≪ μ) (hms : ν ⟂ₘ μ) : ν = 0 := by
  -- From mutual singularity, get the separating set A
  rcases hms with ⟨A, hA_meas, hνA, hμAc⟩
  -- Show ν = 0 by showing ν(s) = 0 for all measurable s
  ext s hs
  -- Split s into s ∩ A and s ∩ Aᶜ
  have hsplit : s = (s ∩ A) ∪ (s ∩ Aᶜ) := by rw [inter_union_compl]
  have hdisj : Disjoint (s ∩ A) (s ∩ Aᶜ) := by
    rw [Set.disjoint_iff]
    intro x ⟨⟨_, hxA⟩, ⟨_, hxAc⟩⟩
    exact hxAc hxA
  calc ν s = ν ((s ∩ A) ∪ (s ∩ Aᶜ)) := by rw [← hsplit]
    _ = ν (s ∩ A) + ν (s ∩ Aᶜ) := measure_union hdisj (hs.inter hA_meas.compl)
    _ = 0 + 0 := by
        congr 1
        -- ν(s ∩ A) ≤ ν(A) = 0
        · exact le_antisymm (measure_mono inter_subset_right |>.trans (le_of_eq hνA)) (zero_le _)
        -- ν(s ∩ Aᶜ) = 0 because μ(s ∩ Aᶜ) ≤ μ(Aᶜ) = 0 and ν ≪ μ
        · have hμ : μ (s ∩ Aᶜ) ≤ μ Aᶜ := measure_mono inter_subset_right
          exact hac (hμ.trans (le_of_eq hμAc) |>.antisymm (zero_le _))
    _ = 0 := add_zero 0

/-- Transitivity of absolute continuity. -/
theorem absolutelyContinuous_trans {ρ : Measure α} (hνμ : ν ≪ μ) (hμρ : μ ≪ ρ) : ν ≪ ρ :=
  hνμ.trans hμρ

end AbsolutelyContinuous

/-! ## Part 4: The Lebesgue Decomposition Theorem

Every σ-finite measure ν can be uniquely decomposed as ν = νₛ + νₐc where:
- νₛ ⟂ μ (the singular part)
- νₐc ≪ μ (the absolutely continuous part)
- νₐc = f • μ for some measurable f (the Radon-Nikodym derivative)

This is Theorem 4.20 in the lecture notes.
-/

section LebesgueDecomposition

variable {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]

/-- The Lebesgue Decomposition: ν = νₛ + (dν/dμ) • μ where νₛ ⟂ μ.
This is Theorem 4.20 in the lecture notes. -/
theorem lebesgue_decomposition :
    ν = ν.singularPart μ + μ.withDensity (ν.rnDeriv μ) :=
  ν.haveLebesgueDecomposition_add μ

/-- The singular part is mutually singular to μ. -/
theorem singularPart_mutuallySingular' (μ ν : Measure α) : ν.singularPart μ ⟂ₘ μ :=
  ν.mutuallySingular_singularPart μ

/-- The Radon-Nikodym derivative is measurable. -/
theorem rnDeriv_measurable' (μ ν : Measure α) : Measurable (ν.rnDeriv μ) :=
  Measure.measurable_rnDeriv ν μ

/-- The absolutely continuous part is indeed absolutely continuous. -/
theorem withDensity_rnDeriv_ac (μ ν : Measure α) : μ.withDensity (ν.rnDeriv μ) ≪ μ :=
  withDensity_absolutelyContinuous μ (ν.rnDeriv μ)

end LebesgueDecomposition

/-! ## Part 5: The Radon-Nikodym Theorem

The main theorem: for σ-finite measures, ν ≪ μ if and only if ν has a density
with respect to μ (i.e., ν = f • μ for some measurable f ≥ 0).

The function f = dν/dμ is called the **Radon-Nikodym derivative**.

This is Corollary 4.23 in the lecture notes.
-/

section RadonNikodym

variable {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]

/-- The Radon-Nikodym Theorem: ν ≪ μ iff ν has a density with respect to μ.

Proof sketch:
(⇐) If ν = f • μ, then μ(A) = 0 implies ν(A) = ∫_A f dμ = 0. Easy.

(⇒) By Lebesgue decomposition: ν = νₛ + f • μ where νₛ ⟂ μ.
    Since ν ≪ μ, we need νₛ ≪ μ.
    But νₛ ⟂ μ (by definition), so νₛ ≪ μ ∧ νₛ ⟂ μ implies νₛ = 0.
    Therefore ν = f • μ.

This is Corollary 4.23 (Radon-Nikodym) in the lecture notes.
-/
theorem radon_nikodym :
    ν ≪ μ ↔ ∃ f : α → ℝ≥0∞, Measurable f ∧ ν = μ.withDensity f := by
  constructor
  · -- Direction (⇒): Absolute continuity implies existence of density
    intro hac
    -- The Radon-Nikodym derivative provides the density
    use ν.rnDeriv μ
    constructor
    · exact Measure.measurable_rnDeriv ν μ
    · -- By Lebesgue decomposition: ν = νₛ + f • μ
      have hdecomp := lebesgue_decomposition (μ := μ) (ν := ν)
      -- νₛ ⟂ μ
      have hms := singularPart_mutuallySingular' (μ := μ) (ν := ν)
      -- Need to show νₛ = 0
      -- νₛ ≪ μ because νₛ ≤ ν and ν ≪ μ
      have hac_singular : ν.singularPart μ ≪ μ := by
        intro s hs
        -- ν.singularPart μ s ≤ ν s
        have h : ν.singularPart μ s ≤ ν s := by
          calc ν.singularPart μ s
              ≤ ν.singularPart μ s + μ.withDensity (ν.rnDeriv μ) s :=
                le_add_of_nonneg_right (zero_le _)
            _ = (ν.singularPart μ + μ.withDensity (ν.rnDeriv μ)) s :=
                (Measure.add_apply _ _ _).symm
            _ = ν s := by rw [← hdecomp]
        -- Since ν ≪ μ and μ s = 0, we have ν s = 0
        have hν : ν s = 0 := hac hs
        exact le_antisymm (h.trans (le_of_eq hν)) (zero_le _)
      -- Since νₛ ≪ μ and νₛ ⟂ μ, we have νₛ = 0
      have hzero := eq_zero_of_ac_of_mutuallySingular hac_singular hms
      -- Therefore ν = f • μ
      calc ν = ν.singularPart μ + μ.withDensity (ν.rnDeriv μ) := hdecomp
        _ = 0 + μ.withDensity (ν.rnDeriv μ) := by rw [hzero]
        _ = μ.withDensity (ν.rnDeriv μ) := zero_add _
  · -- Direction (⇐): Existence of density implies absolute continuity
    rintro ⟨f, _, hf_eq⟩
    rw [hf_eq]
    exact withDensity_absolutelyContinuous μ f

/-- Corollary: If ν ≪ μ, then μ.withDensity (ν.rnDeriv μ) = ν. -/
theorem withDensity_rnDeriv_eq' (hac : ν ≪ μ) :
    μ.withDensity (ν.rnDeriv μ) = ν :=
  Measure.withDensity_rnDeriv_eq ν μ hac

/-- The Radon-Nikodym derivative is unique almost everywhere. -/
theorem rnDeriv_unique (μ : Measure α) [SigmaFinite μ] {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hf_eq : μ.withDensity f = μ.withDensity g) :
    f =ᵐ[μ] g := by
  -- This follows from the uniqueness properties of withDensity
  -- The proof uses that equal measures have equal densities a.e.
  exact (withDensity_eq_iff_of_sigmaFinite hf.aemeasurable hg.aemeasurable).mp hf_eq

end RadonNikodym

/-! ## Part 6: Applications

Some important consequences of the Radon-Nikodym theorem.
-/

section Applications

variable {μ ν ρ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]

/-- Chain rule for Radon-Nikodym derivatives.
If ν ≪ μ, then ν.rnDeriv μ * μ.rnDeriv ρ =ᵐ[ρ] ν.rnDeriv ρ. -/
theorem rnDeriv_chain (hνμ : ν ≪ μ) :
    ν.rnDeriv μ * μ.rnDeriv ρ =ᵐ[ρ] ν.rnDeriv ρ :=
  Measure.rnDeriv_mul_rnDeriv hνμ

/-- Self-derivative: ν.rnDeriv ν = 1 a.e. -/
theorem rnDeriv_self : ν.rnDeriv ν =ᵐ[ν] 1 :=
  Measure.rnDeriv_self ν

end Applications

/-! ## Summary

We have established the complete chain of results leading to the Radon-Nikodym theorem:

1. **Hahn Decomposition** (Theorem 4.13): Every signed measure s decomposes the space
   into a positive set P and a negative set N = Pᶜ.

2. **Jordan Decomposition** (Theorem 4.19): Every signed measure s can be uniquely
   written as s = s⁺ - s⁻ where s⁺ ⟂ s⁻ are positive measures.

3. **Lebesgue Decomposition** (Theorem 4.20): Every σ-finite measure ν decomposes as
   ν = νₛ + νₐc where νₛ ⟂ μ and νₐc ≪ μ.

4. **Radon-Nikodym Theorem** (Corollary 4.23): For σ-finite measures:
   ν ≪ μ  ↔  ∃ f : α → [0,∞], Measurable f ∧ ν = f • μ

The Radon-Nikodym derivative dν/dμ is:
- Unique up to μ-a.e. equality
- Satisfies the chain rule: d(ν)/d(ρ) = (dν/dμ) · (dμ/dρ)
- Fundamental in probability (conditional expectation), statistics (likelihood ratios),
  and functional analysis (representation theorems)
-/

end Project

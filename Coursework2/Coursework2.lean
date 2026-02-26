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

Formalisation of the Radon-Nikodym theorem via the chain:
  Hahn Decomposition → Jordan Decomposition → Lebesgue Decomposition → Radon-Nikodym.

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

The Hahn decomposition theorem partitions the space into a positive set P and
a negative set Pᶜ for any signed measure s (Theorem 4.13).
-/

section HahnDecomposition

variable {s : SignedMeasure α}

/-- The Hahn Decomposition Theorem (Theorem 4.13). -/
theorem hahn_decomposition_exists :
    ∃ (P : Set α), MeasurableSet P ∧ 0 ≤[P] s ∧ s ≤[Pᶜ] 0 :=
  SignedMeasure.exists_compl_positive_negative s

/-- A set of negative measure contains a negative subset (Lemma 4.16). -/
theorem exists_negative_subset_of_negative_measure {i : Set α} (hi_neg : s i < 0) :
    ∃ j ⊆ i, MeasurableSet j ∧ s ≤[j] 0 ∧ s j < 0 := by
  obtain ⟨j, hj_meas, hji, hj_neg, hj_val⟩ := SignedMeasure.exists_subset_restrict_nonpos hi_neg
  exact ⟨j, hji, hj_meas, hj_neg, hj_val⟩

end HahnDecomposition

/-! ## Part 2: The Jordan Decomposition

Every signed measure decomposes as s = s⁺ - s⁻ for mutually singular positive
measures s⁺, s⁻ (Theorem 4.19).
-/

section JordanDecomposition

variable {s : SignedMeasure α}

noncomputable def positivePart (s : SignedMeasure α) : Measure α :=
  s.toJordanDecomposition.posPart

noncomputable def negativePart (s : SignedMeasure α) : Measure α :=
  s.toJordanDecomposition.negPart

instance (s : SignedMeasure α) : IsFiniteMeasure (positivePart s) :=
  s.toJordanDecomposition.posPart_finite

instance (s : SignedMeasure α) : IsFiniteMeasure (negativePart s) :=
  s.toJordanDecomposition.negPart_finite

/-- s = s⁺ - s⁻ (Theorem 4.19). -/
theorem jordan_decomposition_eq :
    s = (positivePart s).toSignedMeasure - (negativePart s).toSignedMeasure := by
  unfold positivePart negativePart
  exact s.toSignedMeasure_toJordanDecomposition.symm

theorem jordan_parts_mutuallySingular :
    positivePart s ⟂ₘ negativePart s := by
  unfold positivePart negativePart
  exact s.toJordanDecomposition.mutuallySingular

/-- |s| = s⁺ + s⁻. -/
noncomputable def totalVariation (s : SignedMeasure α) : Measure α :=
  positivePart s + negativePart s

end JordanDecomposition

/-! ## Part 3: Absolute Continuity and Mutual Singularity -/

section AbsolutelyContinuous

variable {μ ν : Measure α}

lemma ac_def : ν ≪ μ ↔ ∀ s, μ s = 0 → ν s = 0 :=
  Iff.rfl

theorem absolutelyContinuous_withDensity (f : α → ℝ≥0∞) :
    μ.withDensity f ≪ μ :=
  withDensity_absolutelyContinuous μ f

theorem mutuallySingular_symm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ :=
  ⟨Measure.MutuallySingular.symm, Measure.MutuallySingular.symm⟩

/-- ν ≪ μ and ν ⟂ μ together force ν = 0. From the separating set A (with ν(A) = 0,
μ(Aᶜ) = 0), any measurable s splits as (s ∩ A) ∪ (s ∩ Aᶜ) and both pieces vanish. -/
theorem eq_zero_of_ac_of_mutuallySingular (hac : ν ≪ μ) (hms : ν ⟂ₘ μ) : ν = 0 := by
  rcases hms with ⟨A, hA_meas, hνA, hμAc⟩
  ext s hs
  have hsplit : s = (s ∩ A) ∪ (s ∩ Aᶜ) := by rw [inter_union_compl]
  have hdisj : Disjoint (s ∩ A) (s ∩ Aᶜ) := by
    rw [Set.disjoint_iff]
    intro x ⟨⟨_, hxA⟩, ⟨_, hxAc⟩⟩
    exact hxAc hxA
  calc ν s = ν ((s ∩ A) ∪ (s ∩ Aᶜ)) := by rw [← hsplit]
    _ = ν (s ∩ A) + ν (s ∩ Aᶜ) := measure_union hdisj (hs.inter hA_meas.compl)
    _ = 0 + 0 := by
        congr 1
        · exact le_antisymm (measure_mono inter_subset_right |>.trans (le_of_eq hνA)) (zero_le _)
        · have hμ : μ (s ∩ Aᶜ) ≤ μ Aᶜ := measure_mono inter_subset_right
          exact hac (hμ.trans (le_of_eq hμAc) |>.antisymm (zero_le _))
    _ = 0 := add_zero 0

theorem absolutelyContinuous_trans {ρ : Measure α} (hνμ : ν ≪ μ) (hμρ : μ ≪ ρ) : ν ≪ ρ :=
  hνμ.trans hμρ

end AbsolutelyContinuous

/-! ## Part 4: The Lebesgue Decomposition Theorem

ν = νₛ + (dν/dμ) • μ where νₛ ⟂ μ (Theorem 4.20).
-/

section LebesgueDecomposition

variable {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]

theorem lebesgue_decomposition :
    ν = ν.singularPart μ + μ.withDensity (ν.rnDeriv μ) :=
  ν.haveLebesgueDecomposition_add μ

theorem singularPart_mutuallySingular' (μ ν : Measure α) : ν.singularPart μ ⟂ₘ μ :=
  ν.mutuallySingular_singularPart μ

theorem rnDeriv_measurable' (μ ν : Measure α) : Measurable (ν.rnDeriv μ) :=
  Measure.measurable_rnDeriv ν μ

theorem withDensity_rnDeriv_ac (μ ν : Measure α) : μ.withDensity (ν.rnDeriv μ) ≪ μ :=
  withDensity_absolutelyContinuous μ (ν.rnDeriv μ)

end LebesgueDecomposition

/-! ## Part 5: The Radon-Nikodym Theorem

ν ≪ μ ↔ ∃ f, ν = f • μ for σ-finite measures (Corollary 4.23).
-/

section RadonNikodym

variable {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]

/-- The Radon-Nikodym Theorem (Corollary 4.23).
(⇐) Immediate from `withDensity_absolutelyContinuous`.
(⇒) Lebesgue gives ν = νₛ + f • μ with νₛ ⟂ μ. Since νₛ ≤ ν ≪ μ we get νₛ ≪ μ,
    and `eq_zero_of_ac_of_mutuallySingular` forces νₛ = 0. -/
theorem radon_nikodym :
    ν ≪ μ ↔ ∃ f : α → ℝ≥0∞, Measurable f ∧ ν = μ.withDensity f := by
  constructor
  · intro hac
    use ν.rnDeriv μ
    constructor
    · exact Measure.measurable_rnDeriv ν μ
    · have hdecomp := lebesgue_decomposition (μ := μ) (ν := ν)
      have hms := singularPart_mutuallySingular' (μ := μ) (ν := ν)
      have hac_singular : ν.singularPart μ ≪ μ := by
        intro s hs
        have h : ν.singularPart μ s ≤ ν s := by
          calc ν.singularPart μ s
              ≤ ν.singularPart μ s + μ.withDensity (ν.rnDeriv μ) s :=
                le_add_of_nonneg_right (zero_le _)
            _ = (ν.singularPart μ + μ.withDensity (ν.rnDeriv μ)) s :=
                (Measure.add_apply _ _ _).symm
            _ = ν s := by rw [← hdecomp]
        exact le_antisymm (h.trans (le_of_eq (hac hs))) (zero_le _)
      have hzero := eq_zero_of_ac_of_mutuallySingular hac_singular hms
      calc ν = ν.singularPart μ + μ.withDensity (ν.rnDeriv μ) := hdecomp
        _ = 0 + μ.withDensity (ν.rnDeriv μ) := by rw [hzero]
        _ = μ.withDensity (ν.rnDeriv μ) := zero_add _
  · rintro ⟨f, _, hf_eq⟩
    rw [hf_eq]
    exact withDensity_absolutelyContinuous μ f

theorem withDensity_rnDeriv_eq' (hac : ν ≪ μ) :
    μ.withDensity (ν.rnDeriv μ) = ν :=
  Measure.withDensity_rnDeriv_eq ν μ hac

/-- The Radon-Nikodym derivative is unique μ-a.e. -/
theorem rnDeriv_unique (μ : Measure α) [SigmaFinite μ] {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hf_eq : μ.withDensity f = μ.withDensity g) :
    f =ᵐ[μ] g :=
  (withDensity_eq_iff_of_sigmaFinite hf.aemeasurable hg.aemeasurable).mp hf_eq

end RadonNikodym

/-! ## Part 6: Applications -/

section Applications

variable {μ ν ρ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]

/-- Chain rule: dν/dμ · dμ/dρ = dν/dρ  ρ-a.e. -/
theorem rnDeriv_chain (hνμ : ν ≪ μ) :
    ν.rnDeriv μ * μ.rnDeriv ρ =ᵐ[ρ] ν.rnDeriv ρ :=
  Measure.rnDeriv_mul_rnDeriv hνμ

theorem rnDeriv_self : ν.rnDeriv ν =ᵐ[ν] 1 :=
  Measure.rnDeriv_self ν

end Applications

end Project

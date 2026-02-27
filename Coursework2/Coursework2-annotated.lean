/-
  ANNOTATED VERSION — for oral exam prep.
  Every line explained. Read this alongside the real Coursework2.lean.
-/
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- `open scoped` brings NOTATIONS only (≪, ⟂ₘ, ℝ≥0∞) without flooding the namespace.
-- `open` brings NAMES (so we write `range` not `Set.range`).
open scoped MeasureTheory ENNReal NNReal
open Set Filter MeasureTheory

-- Everything lives in `Project` to avoid clashing with Mathlib names.
namespace Project

-- {α : Type*}  → α is an implicit type (Lean infers it). Type* = any universe.
-- [MeasurableSpace α] → α has a σ-algebra (type class; Lean finds it automatically).
variable {α : Type*} [MeasurableSpace α]

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART 1: HAHN DECOMPOSITION
-- Math: every signed measure has a positive/negative partition.
-- Difficulty: TRIVIAL (1-2 lines, just calling Mathlib).
-- ═══════════════════════════════════════════════════════════════════════════════

section HahnDecomposition

-- {s : SignedMeasure α} → s is an implicit signed measure (inferred from usage).
variable {s : SignedMeasure α}

-- STATEMENT: ∃ P measurable, s is ≥0 on P and ≤0 on Pᶜ.
-- PROOF: one direct call to Mathlib.
-- "0 ≤[P] s" means: for every measurable B ⊆ P, s(B) ≥ 0.
theorem hahn_decomposition_exists :
    ∃ (P : Set α), MeasurableSet P ∧ 0 ≤[P] s ∧ s ≤[Pᶜ] 0 :=
  SignedMeasure.exists_compl_positive_negative s
  -- ^ This IS the proof. No tactics needed. Just the Mathlib lemma name.

-- STATEMENT: if s(i) < 0, there's a negative subset j ⊆ i with s(j) < 0.
-- PROOF: Mathlib returns fields in order (j, measurable, subset, neg, val)
--        but we want (j, subset, measurable, neg, val).
--        So we unpack with `obtain` and repack with `exact ⟨...⟩`.
theorem exists_negative_subset_of_negative_measure {i : Set α} (hi_neg : s i < 0) :
    ∃ j ⊆ i, MeasurableSet j ∧ s ≤[j] 0 ∧ s j < 0 := by
  obtain ⟨j, hj_meas, hji, hj_neg, hj_val⟩ :=
    SignedMeasure.exists_subset_restrict_nonpos hi_neg
  -- Now we have: j (the set), hj_meas (measurable), hji (j ⊆ i),
  --              hj_neg (s ≤[j] 0), hj_val (s j < 0)
  exact ⟨j, hji, hj_meas, hj_neg, hj_val⟩
  -- ^ Repack in the order our ∃ statement expects: j, then ⊆, then the rest.

end HahnDecomposition

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART 2: JORDAN DECOMPOSITION
-- Math: s = s⁺ - s⁻ where s⁺ ⟂ s⁻.
-- Difficulty: LOW (unfold + exact pattern).
-- ═══════════════════════════════════════════════════════════════════════════════

section JordanDecomposition

variable {s : SignedMeasure α}

-- `noncomputable` because toJordanDecomposition uses classical choice internally.
-- These are just WRAPPER DEFINITIONS around Mathlib's internal representation.
noncomputable def positivePart (s : SignedMeasure α) : Measure α :=
  s.toJordanDecomposition.posPart

noncomputable def negativePart (s : SignedMeasure α) : Measure α :=
  s.toJordanDecomposition.negPart

-- `instance` registers a fact with Lean's type class system.
-- After this, anywhere that needs [IsFiniteMeasure (positivePart s)],
-- Lean finds it automatically.
instance (s : SignedMeasure α) : IsFiniteMeasure (positivePart s) :=
  s.toJordanDecomposition.posPart_finite

instance (s : SignedMeasure α) : IsFiniteMeasure (negativePart s) :=
  s.toJordanDecomposition.negPart_finite

-- PROOF PATTERN: unfold + exact + .symm
-- Step 1: `unfold` expands our wrapper names so Lean sees the raw Mathlib types.
-- Step 2: `exact` provides the Mathlib proof.
-- Step 3: `.symm` flips the equality direction (Mathlib has s⁺-s⁻=s, we want s=s⁺-s⁻).
-- WITHOUT `unfold`, Lean sees `positivePart s` ≠ `toJordanDecomposition.posPart`
-- even though they're definitionally equal — `exact` is picky about syntax.
theorem jordan_decomposition_eq :
    s = (positivePart s).toSignedMeasure - (negativePart s).toSignedMeasure := by
  unfold positivePart negativePart
  exact s.toSignedMeasure_toJordanDecomposition.symm

-- Same pattern, no .symm needed this time.
theorem jordan_parts_mutuallySingular :
    positivePart s ⟂ₘ negativePart s := by
  unfold positivePart negativePart
  exact s.toJordanDecomposition.mutuallySingular

noncomputable def totalVariation (s : SignedMeasure α) : Measure α :=
  positivePart s + negativePart s

end JordanDecomposition

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART 3: ABSOLUTE CONTINUITY + MUTUAL SINGULARITY + KEY LEMMA
-- The key lemma is YOUR MAIN ORIGINAL PROOF. Know it cold.
-- ═══════════════════════════════════════════════════════════════════════════════

section AbsolutelyContinuous

-- No [SigmaFinite] here! The key lemma works for arbitrary measures.
-- This was a deliberate design choice (see Challenges in the report).
variable {μ ν : Measure α}

-- `Iff.rfl` means the two sides of ↔ are DEFINITIONALLY equal.
-- ν ≪ μ literally IS ∀ s, μ s = 0 → ν s = 0. No unfolding needed.
lemma ac_def : ν ≪ μ ↔ ∀ s, μ s = 0 → ν s = 0 :=
  Iff.rfl

-- Direct Mathlib call. "A measure built from a density is always AC."
theorem absolutelyContinuous_withDensity (f : α → ℝ≥0∞) :
    μ.withDensity f ≪ μ :=
  withDensity_absolutelyContinuous μ f

-- ⟨proof₁, proof₂⟩ is the anonymous constructor for ↔.
-- Each component is Measure.MutuallySingular.symm (mutual singularity is symmetric).
theorem mutuallySingular_symm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ :=
  ⟨Measure.MutuallySingular.symm, Measure.MutuallySingular.symm⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- THE KEY LEMMA — know EVERY line for the oral exam.
--
-- Math: If ν ≪ μ and ν ⟂ μ, then ν = 0.
-- Strategy: Get separating set A from ⟂. For any measurable s,
--           split s = (s∩A) ∪ (s∩Aᶜ). Both pieces have ν-measure 0.
-- ═══════════════════════════════════════════════════════════════════════════════

theorem eq_zero_of_ac_of_mutuallySingular (hac : ν ≪ μ) (hms : ν ⟂ₘ μ) : ν = 0 := by
  -- STEP 1: Unpack mutual singularity into its 4 fields.
  -- hms : ν ⟂ₘ μ is a structure with:
  --   A         : Set α          (the separating set)
  --   hA_meas   : MeasurableSet A
  --   hνA       : ν A = 0        (ν is zero on A)
  --   hμAc      : μ Aᶜ = 0       (μ is zero on Aᶜ)
  rcases hms with ⟨A, hA_meas, hνA, hμAc⟩

  -- STEP 2: Measure extensionality.
  -- To prove ν = 0 (two measures are equal), we show they agree on every
  -- measurable set. `ext s hs` introduces an arbitrary measurable set s
  -- and its measurability proof hs. Goal becomes: ν s = 0 s  (i.e., ν s = 0).
  ext s hs

  -- STEP 3: Split s into two pieces.
  -- s = (s ∩ A) ∪ (s ∩ Aᶜ)  — this is just set theory (inter_union_compl).
  have hsplit : s = (s ∩ A) ∪ (s ∩ Aᶜ) := by rw [inter_union_compl]

  -- STEP 4: Prove the two pieces are disjoint.
  -- A point can't be in both A and Aᶜ.
  -- Set.disjoint_iff reduces Disjoint to: if x ∈ both, derive False.
  -- We destructure: x ∈ (s∩A) gives (_, hxA), x ∈ (s∩Aᶜ) gives (_, hxAc).
  -- hxAc says x ∈ Aᶜ, but hxA says x ∈ A — contradiction.
  have hdisj : Disjoint (s ∩ A) (s ∩ Aᶜ) := by
    rw [Set.disjoint_iff]
    intro x ⟨⟨_, hxA⟩, ⟨_, hxAc⟩⟩
    exact hxAc hxA

  -- STEP 5: The main calc chain.
  calc ν s
      -- (a) Rewrite s as the union (using hsplit backwards).
      = ν ((s ∩ A) ∪ (s ∩ Aᶜ)) := by rw [← hsplit]
      -- (b) Split the measure of a disjoint union into a sum.
      --     measure_union needs: Disjoint proof + MeasurableSet for second arg.
      --     hs.inter hA_meas.compl = MeasurableSet (s ∩ Aᶜ).
    _ = ν (s ∩ A) + ν (s ∩ Aᶜ) := measure_union hdisj (hs.inter hA_meas.compl)
      -- (c) Show both summands are 0.
      --     congr 1: "the outer function (+) is the same, prove each arg equal."
      --     Creates two subgoals: ν(s∩A) = 0 and ν(s∩Aᶜ) = 0.
    _ = 0 + 0 := by
        congr 1
        -- SUBGOAL 1: ν(s ∩ A) = 0
        -- By monotonicity: s∩A ⊆ A, so ν(s∩A) ≤ ν(A) = 0.
        -- le_antisymm + zero_le closes it to = 0.
        · exact le_antisymm (measure_mono inter_subset_right |>.trans (le_of_eq hνA)) (zero_le _)
          -- Breakdown:
          --   measure_mono inter_subset_right  →  ν(s∩A) ≤ ν(A)
          --   |>.trans (le_of_eq hνA)          →  ν(s∩A) ≤ 0     (since ν(A) = 0)
          --   le_antisymm ... (zero_le _)      →  ν(s∩A) = 0     (0 ≤ ν(s∩A) always)

        -- SUBGOAL 2: ν(s ∩ Aᶜ) = 0
        -- By monotonicity: s∩Aᶜ ⊆ Aᶜ, so μ(s∩Aᶜ) ≤ μ(Aᶜ) = 0.
        -- Chain to μ(s∩Aᶜ) = 0, then apply absolute continuity.
        · have hμ : μ (s ∩ Aᶜ) ≤ μ Aᶜ := measure_mono inter_subset_right
          exact hac (hμ.trans (le_of_eq hμAc) |>.antisymm (zero_le _))
          -- Breakdown:
          --   measure_mono inter_subset_right  →  μ(s∩Aᶜ) ≤ μ(Aᶜ)
          --   .trans (le_of_eq hμAc)           →  μ(s∩Aᶜ) ≤ 0
          --   .antisymm (zero_le _)            →  μ(s∩Aᶜ) = 0
          --   hac (...)                         →  ν(s∩Aᶜ) = 0   (by ν ≪ μ)

    _ = 0 := add_zero 0   -- 0 + 0 = 0. Done.

-- Transitivity of ≪. Dot notation: hνμ.trans hμρ calls the .trans method.
theorem absolutelyContinuous_trans {ρ : Measure α} (hνμ : ν ≪ μ) (hμρ : μ ≪ ρ) : ν ≪ ρ :=
  hνμ.trans hμρ

end AbsolutelyContinuous

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART 4: LEBESGUE DECOMPOSITION
-- Four facts extracted from Mathlib for Part 5 to use.
-- Difficulty: TRIVIAL (all one-liners).
-- ═══════════════════════════════════════════════════════════════════════════════

section LebesgueDecomposition

-- NOW we need σ-finiteness. [SigmaFinite μ] is a type class.
-- Lean uses it to auto-synthesise HaveLebesgueDecomposition instances.
variable {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]

-- Fact 1: ν = νₛ + f·μ  (the decomposition identity)
theorem lebesgue_decomposition :
    ν = ν.singularPart μ + μ.withDensity (ν.rnDeriv μ) :=
  ν.haveLebesgueDecomposition_add μ

-- Fact 2: νₛ ⟂ μ  (singular part is singular)
-- Explicit args (μ ν : Measure α) because both are the same type.
theorem singularPart_mutuallySingular' (μ ν : Measure α) : ν.singularPart μ ⟂ₘ μ :=
  ν.mutuallySingular_singularPart μ

-- Fact 3: dν/dμ is measurable
theorem rnDeriv_measurable' (μ ν : Measure α) : Measurable (ν.rnDeriv μ) :=
  Measure.measurable_rnDeriv ν μ

-- Fact 4: f·μ ≪ μ  (density measure is AC)
theorem withDensity_rnDeriv_ac (μ ν : Measure α) : μ.withDensity (ν.rnDeriv μ) ≪ μ :=
  withDensity_absolutelyContinuous μ (ν.rnDeriv μ)

end LebesgueDecomposition

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART 5: RADON-NIKODYM THEOREM
-- The main theorem. Forward direction is non-trivial.
-- ═══════════════════════════════════════════════════════════════════════════════

section RadonNikodym

variable {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]

-- STATEMENT: ν ≪ μ  ↔  ∃ measurable f, ν = f·μ
theorem radon_nikodym :
    ν ≪ μ ↔ ∃ f : α → ℝ≥0∞, Measurable f ∧ ν = μ.withDensity f := by

  -- Split the ↔ into two goals: ⇒ and ⇐.
  constructor

  -- ════════ FORWARD DIRECTION (⇒): ν ≪ μ implies density exists ════════
  · intro hac
    -- hac : ν ≪ μ  (our hypothesis)

    -- Witness: the Radon-Nikodym derivative from Mathlib.
    use ν.rnDeriv μ

    -- Split the ∧: need (1) Measurable f, and (2) ν = μ.withDensity f.
    constructor

    -- (1) Measurability: direct Mathlib call.
    · exact Measure.measurable_rnDeriv ν μ

    -- (2) The identity ν = μ.withDensity (ν.rnDeriv μ).
    · -- Load the Lebesgue decomposition and singular-part singularity.
      -- Named args (μ := μ) (ν := ν) needed because both are Measure α
      -- and Lean can't tell which is which.
      have hdecomp := lebesgue_decomposition (μ := μ) (ν := ν)
      -- hdecomp : ν = ν.singularPart μ + μ.withDensity (ν.rnDeriv μ)

      have hms := singularPart_mutuallySingular' (μ := μ) (ν := ν)
      -- hms : ν.singularPart μ ⟂ₘ μ

      -- KEY STEP: show the singular part is absolutely continuous w.r.t. μ.
      -- Then key lemma (AC + singular ⟹ zero) kills it.
      have hac_singular : ν.singularPart μ ≪ μ := by
        -- Unfold ≪: take any set s with μ(s) = 0, show νₛ(s) = 0.
        intro s hs
        -- hs : μ s = 0

        -- First show νₛ(s) ≤ ν(s).
        have h : ν.singularPart μ s ≤ ν s := by
          calc ν.singularPart μ s
              -- νₛ(s) ≤ νₛ(s) + withDensity(s)  [adding non-negative term]
              ≤ ν.singularPart μ s + μ.withDensity (ν.rnDeriv μ) s :=
                le_add_of_nonneg_right (zero_le _)
              -- ... = (νₛ + withDensity)(s)  [rewrite point eval of sum measure]
            _ = (ν.singularPart μ + μ.withDensity (ν.rnDeriv μ)) s :=
                (Measure.add_apply _ _ _).symm
              -- ... = ν(s)  [by Lebesgue decomposition]
            _ = ν s := by rw [← hdecomp]

        -- Now: νₛ(s) ≤ ν(s) and ν(s) = 0 (from hac and hs).
        -- Chain: νₛ(s) ≤ ν(s) = 0, then le_antisymm with zero_le.
        exact le_antisymm (h.trans (le_of_eq (hac hs))) (zero_le _)
        -- h.trans (le_of_eq (hac hs))  →  νₛ(s) ≤ 0
        -- le_antisymm ... (zero_le _)  →  νₛ(s) = 0

      -- Apply the key lemma: νₛ ≪ μ + νₛ ⟂ μ ⟹ νₛ = 0.
      have hzero := eq_zero_of_ac_of_mutuallySingular hac_singular hms
      -- hzero : ν.singularPart μ = 0

      -- Final calc: substitute νₛ = 0 into the decomposition.
      calc ν = ν.singularPart μ + μ.withDensity (ν.rnDeriv μ) := hdecomp
        _ = 0 + μ.withDensity (ν.rnDeriv μ) := by rw [hzero]
        _ = μ.withDensity (ν.rnDeriv μ) := zero_add _

  -- ════════ REVERSE DIRECTION (⇐): density exists implies ν ≪ μ ════════
  -- This is the easy direction.
  · -- rintro = intro + rcases. Unpacks ∃ f, Measurable f ∧ ν = μ.withDensity f.
    -- f is the density, _ discards measurability (not needed), hf_eq is the identity.
    rintro ⟨f, _, hf_eq⟩
    -- Rewrite ν as μ.withDensity f.
    rw [hf_eq]
    -- μ.withDensity f ≪ μ is a library fact.
    exact withDensity_absolutelyContinuous μ f

-- Corollary: if ν ≪ μ, then μ.withDensity (ν.rnDeriv μ) = ν.
theorem withDensity_rnDeriv_eq' (hac : ν ≪ μ) :
    μ.withDensity (ν.rnDeriv μ) = ν :=
  Measure.withDensity_rnDeriv_eq ν μ hac

-- Uniqueness: if two measurable functions give the same withDensity, they're a.e. equal.
-- .mp extracts the forward direction of the ↔ from withDensity_eq_iff_of_sigmaFinite.
theorem rnDeriv_unique (μ : Measure α) [SigmaFinite μ] {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hf_eq : μ.withDensity f = μ.withDensity g) :
    f =ᵐ[μ] g :=
  (withDensity_eq_iff_of_sigmaFinite hf.aemeasurable hg.aemeasurable).mp hf_eq

end RadonNikodym

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART 6: APPLICATIONS
-- Two standard consequences. Both one-line Mathlib calls.
-- ═══════════════════════════════════════════════════════════════════════════════

section Applications

-- Three measures, three [SigmaFinite] instances (chain rule needs all three).
variable {μ ν ρ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]

-- Chain rule: (dν/dμ) · (dμ/dρ) = dν/dρ  ρ-a.e.
-- =ᵐ[ρ] means "equal ρ-almost everywhere" = they differ on a ρ-null set.
-- Full type: Filter.EventuallyEq (Measure.ae ρ) (ν.rnDeriv μ * μ.rnDeriv ρ) (ν.rnDeriv ρ)
theorem rnDeriv_chain (hνμ : ν ≪ μ) :
    ν.rnDeriv μ * μ.rnDeriv ρ =ᵐ[ρ] ν.rnDeriv ρ :=
  Measure.rnDeriv_mul_rnDeriv hνμ

-- Self-derivative: dν/dν = 1 a.e.
theorem rnDeriv_self : ν.rnDeriv ν =ᵐ[ν] 1 :=
  Measure.rnDeriv_self ν

end Applications

end Project

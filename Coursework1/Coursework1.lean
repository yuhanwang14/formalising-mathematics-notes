/-
Copyright (c) 2026 Yuhan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhan Wang
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# The Cauchy Criterion in ℝ

This file proves that a sequence in ℝ is Cauchy if and only if it converges.

## Main results

- `cauchySeq_isBounded_range`: Cauchy sequences have bounded range.
- `exists_tendsto_subseq_of_bounded`: Bounded sequences have convergent subsequences.
- `tendsto_of_cauchySeq_of_tendsto_subseq`: Cauchy + convergent subsequence ⇒ convergent.
- `cauchySeq_of_tendsto`: Convergent sequences are Cauchy.
- `cauchy_criterion_real_exists_rudin`: The main theorem.

## References

* Walter Rudin, *Principles of Mathematical Analysis*, Chapter 3
-/

open scoped Topology
open Set Filter

namespace Project

/-! ## Part 1: Cauchy ⇒ Convergent -/

/-- Cauchy sequences in ℝ have bounded range.
Split the range into a tail controlled by Cauchy condition and a finite prefix. -/
lemma cauchySeq_isBounded_range {u : ℕ → ℝ} (hu : CauchySeq u) :
    Bornology.IsBounded (Set.range u) := by
  classical
  -- Convert the Cauchy condition to the ε-N form
  have hC := Metric.cauchySeq_iff.mp hu
  -- Apply with ε = 1 to get the threshold index N
  rcases hC 1 (by norm_num) with ⟨N, hN⟩
  -- Define the finite prefix: the image of {0, 1, ..., N-1} under u
  let prefixSet : Set ℝ := u '' (Set.Iio N)
  -- Show that the full range is contained in the ball ∪ prefix
  have hsub : Set.range u ⊆ Metric.ball (u N) 1 ∪ prefixSet := by
    intro x hx
    -- x is in the range, so x = u(n) for some n
    rcases hx with ⟨n, rfl⟩
    -- Case split on whether n ≥ N or n < N
    by_cases hn : N ≤ n
    · -- Case n ≥ N: u(n) is in the ball B(u_N, 1)
      left
      have : dist (u n) (u N) < 1 := hN n hn N le_rfl
      simpa [Metric.mem_ball] using this
    · -- Case n < N: u(n) is in the finite prefix
      right
      have : n ∈ Set.Iio N := Nat.lt_of_not_ge hn
      exact ⟨n, this, rfl⟩
  -- Ball is bounded (metric space property)
  have hball_bdd : Bornology.IsBounded (Metric.ball (u N) 1 : Set ℝ)
    := Metric.isBounded_ball
  -- Finite prefix is bounded (finite sets are bounded)
  have hprefixSet_bdd : Bornology.IsBounded prefixSet := by
    have : (Set.Iio N).Finite := Set.finite_Iio N
    simpa [prefixSet] using (this.image u).isBounded
  -- Union of bounded sets is bounded, subset of bounded is bounded
  exact (hball_bdd.union hprefixSet_bdd).subset hsub

/-- Bolzano-Weierstrass: bounded sequences in ℝ have convergent subsequences.
Uses compactness of closed balls in ℝ. -/
lemma exists_tendsto_subseq_of_bounded {u : ℕ → ℝ}
    (hb : Bornology.IsBounded (Set.range u)) :
    ∃ a : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) := by
  classical
  -- Find a closed ball containing the entire range
  rcases hb.subset_closedBall (0 : ℝ) with ⟨R, hsub⟩
  -- Every term of the sequence lies in this closed ball
  have hu_in : ∀ n : ℕ, u n ∈ Metric.closedBall (0 : ℝ) R := fun n ↦ hsub ⟨n, rfl⟩
  -- Closed balls in ℝ are compact (uses completeness of ℝ)
  have hK : IsCompact (Metric.closedBall (0 : ℝ) R) := isCompact_closedBall 0 R
  -- Extract a convergent subsequence via sequential compactness
  rcases hK.tendsto_subseq hu_in with ⟨a, _, φ, hφ, hlim⟩
  exact ⟨a, φ, hφ, hlim⟩

/-- A Cauchy sequence with a convergent subsequence converges to the same limit.
Uses ε/2 argument combining Cauchy property with subsequence convergence. -/
lemma tendsto_of_cauchySeq_of_tendsto_subseq {u : ℕ → ℝ} {a : ℝ} {φ : ℕ → ℕ}
    (hu : CauchySeq u) (hφ : StrictMono φ) (hsub : Tendsto (u ∘ φ) atTop (𝓝 a)) :
    Tendsto u atTop (𝓝 a) := by
  -- Rewrite using the ε-N characterisation
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get the Cauchy condition in ε-N form
  have hC := fun δ hδ => Metric.cauchySeq_iff.mp hu δ hδ
  -- From Cauchy: find N such that |u_m - u_n| < ε/2 for m, n ≥ N
  rcases hC (ε / 2) (by linarith) with ⟨N, hN⟩
  -- From subsequence convergence: find K such that |u_{φ(k)} - a| < ε/2 for k ≥ K
  rcases (Metric.tendsto_atTop.mp hsub) (ε / 2) (by linarith) with ⟨K, hK⟩
  -- Since φ is strictly increasing, φ(k) → ∞
  have hφ_atTop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  -- Find K₁ such that φ(k) ≥ N for all k ≥ K₁
  rcases Filter.eventually_atTop.mp (Filter.tendsto_atTop.mp hφ_atTop N) with ⟨K₁, hK₁⟩
  -- Take k₀ = max(K, K₁) to satisfy both conditions
  let k₀ := max K K₁
  -- We claim N works as the threshold for convergence
  refine ⟨N, fun n hn => ?_⟩
  -- h1: |u_n - u_{φ(k₀)}| < ε/2 (from Cauchy)
  have h1 : dist (u n) (u (φ k₀)) < ε / 2 := hN n hn (φ k₀) (hK₁ k₀ (le_max_right K K₁))
  -- h2: |u_{φ(k₀)} - a| < ε/2 (from subsequence convergence)
  have h2 : dist (u (φ k₀)) a < ε / 2 := hK k₀ (le_max_left K K₁)
  -- Combine via triangle inequality
  calc dist (u n) a
      ≤ dist (u n) (u (φ k₀)) + dist (u (φ k₀)) a := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

/-! ## Part 2: Convergent ⇒ Cauchy -/

/-- Convergent sequences are Cauchy.
Standard ε/2 argument using the triangle inequality. -/
lemma cauchySeq_of_tendsto {u : ℕ → ℝ} {a : ℝ} (ha : Tendsto u atTop (𝓝 a))
  : CauchySeq u := by
  -- Rewrite using the ε-N characterisation
  rw [Metric.cauchySeq_iff]
  intro ε hε
  -- From convergence: find N such that |u_n - a| < ε/2 for n ≥ N
  rcases Metric.tendsto_atTop.mp ha (ε / 2) (by linarith) with ⟨N, hN⟩
  -- N works as our threshold
  refine ⟨N, fun m hm n hn => ?_⟩
  -- Triangle inequality: |u_m - u_n| ≤ |u_m - a| + |a - u_n|
  calc dist (u m) (u n)
      ≤ dist (u m) a + dist a (u n) := dist_triangle _ _ _
    _ = dist (u m) a + dist (u n) a := by rw [dist_comm a (u n)]
    _ < ε / 2 + ε / 2 := add_lt_add (hN m hm) (hN n hn)
    _ = ε := by ring

/-! ## Main Theorem -/

/-- The Cauchy criterion: a sequence in ℝ is Cauchy iff it converges.
This characterises completeness of the real numbers. -/
theorem cauchy_criterion_real_exists_rudin (u : ℕ → ℝ) :
    CauchySeq u ↔ ∃ a : ℝ, Tendsto u atTop (𝓝 a) := by
  constructor
  · -- Direction (⇒): Cauchy implies convergent
    intro hu
    -- Step 1: Cauchy ⇒ bounded range
    have hb := cauchySeq_isBounded_range hu
    -- Step 2: Bounded ⇒ convergent subsequence (Bolzano-Weierstrass)
    rcases exists_tendsto_subseq_of_bounded hb with ⟨a, φ, hφ, hsub⟩
    -- Step 3: Cauchy + convergent subsequence ⇒ convergent
    exact ⟨a, tendsto_of_cauchySeq_of_tendsto_subseq hu hφ hsub⟩
  · -- Direction (⇐): Convergent implies Cauchy
    rintro ⟨a, ha⟩
    exact cauchySeq_of_tendsto ha

end Project

/-
Copyright (c) 2026 MA5217 formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MA5217 formalization project (Conway, Chapter VIII)
-/

module

public import Conway.Basic
public import Conway.Geom
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Convex.Segment

/-!
# MA5217 / Conway Chapter VIII, §1: the Cauchy transform of a single line segment

This is the analytic engine of the lecturer's proof of the weak Runge theorem (lecture 13 p.3–4):
the Cauchy transform of a continuous function over a *single* straight line segment `[a,b] ⊆ ℂ`,

    F(z) = ∫₀¹ φ(γ(t)) / (γ(t) - z) · (b - a) dt,   γ(t) = lineMap a b t,

which is Mathlib's `curveIntegral_segment` written out, is approximated uniformly on a set `K`
disjoint from the segment by rational functions with a single pole at the midpoint `z₀` of the
segment.  This is exactly the lecturer's argument:

* "Choose `z₀ ∈ ℂ` with `B̄(z₀; δ/2) ∩ K = ∅`" — the midpoint of a segment shorter than `δ`;
* "the map `z ↦ (2πi)⁻¹ ∫_E φ(w)/(w - z) dw` is holomorphic on `ℂ − E`; by Laurent's theorem it
  has a Laurent expansion about `z₀`" — the expansion is obtained here by hand from the geometric
  series (`Conway.Geom`), and it is a Laurent series in `(z - z₀)⁻¹` with *no constant term* (the
  lecturer's remark that the transform tends to `0` at `∞`);
* "the partial sums `R(z) = Σ_{n=1}^N a₋ₙ (z - z₀)^(-n)` have a pole at `z₀ ∈ ℂ∞ − K` and converge
  normally on `K` to `F`" — this is `Conway.approximable_segIntegral` below.

The normalization `(2πi)⁻¹` is *not* included in `segIntegral`: it is an irrelevant constant for
approximation, and it is supplied once and for all in the statement of the (axiomatized) global
Cauchy representation, `Conway.separationLemma`.
-/

@[expose] public section

open scoped BigOperators Convex
open Set intervalIntegral MeasureTheory Filter AffineMap

namespace Conway

noncomputable section

variable {K : Set ℂ}

/-! ## Integrals along a single line segment -/

/-- The Cauchy transform of `φ` along the line segment from `a` to `b`,

    `segIntegral φ a b z = ∫₀¹ φ(γ(t)) (γ(t) - z)⁻¹ (b - a) dt`,

i.e. `(2πi)⁻¹` times the contour integral `∫_[a,b] φ(w)/(w - z) dw` once the normalizing constant
is supplied: by Mathlib's `curveIntegral_segment` the parametrization is the same
`t ∈ [0,1] ↦ lineMap a b t`. -/
def segIntegral (φ : ℂ → ℂ) (a b z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, φ (lineMap a b t) * (lineMap a b t - z)⁻¹ * (b - a)

/-- The parametrized version of the integrand of `segIntegral`. -/
def segIntegrand (φ : ℂ → ℂ) (a b z : ℂ) : ℝ → ℂ :=
  fun t ↦ φ (lineMap a b t) * (lineMap a b t - z)⁻¹ * (b - a)

/-- The `k`-th Laurent coefficient of the Cauchy transform at `z₀`:

    `segCoeff φ a b z₀ k = ∫₀¹ φ(γ(t)) (γ(t) - z₀)^k (b - a) dt`,

so that the partial sum of the lecturer's `R(z) = Σₙ a₋ₙ (z - z₀)^(-n)` is
`-∑ k in Finset.range (N+1), segCoeff φ a b z₀ k * (z - z₀)⁻¹^(k+1)` (the sign comes from the
minus in the expansion `(w - z)⁻¹ = -Σₖ (w - z₀)^k (z - z₀)^(-k-1) + …`). -/
def segCoeff (φ : ℂ → ℂ) (a b z₀ : ℂ) (k : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..1, φ (lineMap a b t) * (lineMap a b t - z₀) ^ k * (b - a)

/-- **The lecturer's partial sums** `R(z) = Σ_{n=1}^{N+1} a₋ₙ (z - z₀)^(-n)` (lecture 13 p.4) of
the Laurent expansion at `z₀` of the Cauchy transform of the segment `[a,b]`, restricted to `K`.
It is a rational function with a pole of order `≤ N+1` at `z₀`, hence an element of
`PoleAt z₀ K`. -/
def segApprox (K : Set ℂ) (φ : ℂ → ℂ) (a b z₀ : ℂ) (N : ℕ) : ↥K → ℂ :=
  fun z ↦ ∑ k ∈ Finset.range (N + 1), -(segCoeff φ a b z₀ k) * invSub z₀ K z ^ (k + 1)

/-- Continuity of `φ` along the segment `[a,b]`, transported to the parametrization. -/
theorem continuousOn_lineMap {φ : ℂ → ℂ} {a b : ℂ} (hφ : ContinuousOn φ [a -[ℝ] b]) :
    ContinuousOn (fun t : ℝ ↦ φ (lineMap a b t)) (Icc (0 : ℝ) 1) := by
  refine ContinuousOn.comp hφ ?_ ?_
  · exact lineMap_continuous.continuousOn
  · intro t ht
    rw [segment_eq_image_lineMap]
    exact mem_image_of_mem _ ht

/-- A function that is continuous along a segment is bounded there. -/
theorem exists_norm_le_of_continuousOn {φ : ℂ → ℂ} {a b : ℂ}
    (hφ : ContinuousOn φ [a -[ℝ] b]) :
    ∃ M, ∀ t ∈ Icc (0 : ℝ) 1, ‖φ (lineMap a b t)‖ ≤ M := by
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.image_of_continuousOn (continuousOn_lineMap hφ)).isBounded.subset_closedBall
      (0 : ℂ)
  exact ⟨M, fun t ht ↦ by
    have := hM (mem_image_of_mem _ ht)
    simpa [dist_eq_norm, sub_zero] using this⟩

/-- The fundamental estimate for an integral over `[0,1]`: the length of the path is `1`. -/
theorem norm_integral_le_of_forall_norm_le {f : ℝ → ℂ} {C : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ C) : ‖∫ t in (0 : ℝ)..1, f t‖ ≤ C := by
  have hIoc : Set.uIoc (0 : ℝ) (1 : ℝ) = Set.Ioc (0 : ℝ) (1 : ℝ) :=
    uIoc_of_le zero_le_one
  have hI : ∀ t, t ∈ Set.uIoc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 := fun t ht ↦
    by rw [hIoc] at ht; exact ⟨ht.1.le, ht.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    fun t ht ↦ h t (hI t ht)
  rwa [sub_zero, abs_one, mul_one] at h

/-- Each summand of the Laurent expansion is continuous along the segment. -/
theorem continuousOn_segSummand {φ : ℂ → ℂ} {a b z z₀ : ℂ} (hφ : ContinuousOn φ [a -[ℝ] b])
    (k : ℕ) :
    ContinuousOn
      (fun t : ℝ ↦ φ (lineMap a b t) * ((lineMap a b t - z₀) ^ k * (z - z₀)⁻¹ ^ (k + 1)) * (b - a))
      (Icc (0 : ℝ) 1) := by
  have h1 : ContinuousOn (fun t : ℝ ↦ φ (lineMap a b t)) (Icc (0 : ℝ) 1) :=
    continuousOn_lineMap hφ
  have h2 : ContinuousOn (fun t : ℝ ↦ lineMap a b t - z₀) (Icc (0 : ℝ) 1) := by fun_prop
  have h3 : ContinuousOn (fun t : ℝ ↦ (lineMap a b t - z₀) ^ k) (Icc (0 : ℝ) 1) := h2.pow k
  have h4 : ContinuousOn (fun _ : ℝ ↦ (z - z₀)⁻¹ ^ (k + 1)) (Icc (0 : ℝ) 1) := continuousOn_const
  have h5 : ContinuousOn (fun t : ℝ ↦ (lineMap a b t - z₀) ^ k * (z - z₀)⁻¹ ^ (k + 1))
      (Icc (0 : ℝ) 1) := h3.mul h4
  have h6 : ContinuousOn
      (fun t : ℝ ↦ φ (lineMap a b t) * ((lineMap a b t - z₀) ^ k * (z - z₀)⁻¹ ^ (k + 1)))
      (Icc (0 : ℝ) 1) := h1.mul h5
  have h7 : ContinuousOn (fun _ : ℝ ↦ (b - a)) (Icc (0 : ℝ) 1) := continuousOn_const
  exact h6.mul h7

/-- The integrand of `segIntegral` is continuous — hence integrable — off the segment. -/
theorem segIntegral_integrable {φ : ℂ → ℂ} {a b z : ℂ} (hφ : ContinuousOn φ [a -[ℝ] b])
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, lineMap a b t ≠ z) :
    IntervalIntegrable (fun t : ℝ ↦ φ (lineMap a b t) * (lineMap a b t - z)⁻¹ * (b - a))
      volume 0 1 := by
  have h1 : ContinuousOn (fun t : ℝ ↦ φ (lineMap a b t)) (Icc (0 : ℝ) 1) :=
    continuousOn_lineMap hφ
  have h2 : ContinuousOn (fun t : ℝ ↦ lineMap a b t - z) (Icc (0 : ℝ) 1) := by fun_prop
  have h3 : ContinuousOn (fun t : ℝ ↦ (lineMap a b t - z)⁻¹) (Icc (0 : ℝ) 1) :=
    h2.inv₀ fun (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) ↦ sub_ne_zero.mpr (hz t ht)
  have h4 : ContinuousOn (fun t : ℝ ↦ φ (lineMap a b t) * (lineMap a b t - z)⁻¹)
      (Icc (0 : ℝ) 1) := h1.mul h3
  have h5 : ContinuousOn (fun _ : ℝ ↦ (b - a)) (Icc (0 : ℝ) 1) := continuousOn_const
  exact ((h4.mul h5).intervalIntegrable_of_Icc zero_le_one)

/-- The integrand of the `k`-th Laurent coefficient is continuous — hence integrable. -/
theorem segCoeff_integrable {φ : ℂ → ℂ} {a b z₀ : ℂ} (hφ : ContinuousOn φ [a -[ℝ] b]) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ φ (lineMap a b t) * (lineMap a b t - z₀) ^ k * (b - a))
      volume 0 1 := by
  have h1 : ContinuousOn (fun t : ℝ ↦ φ (lineMap a b t)) (Icc (0 : ℝ) 1) :=
    continuousOn_lineMap hφ
  have h2 : ContinuousOn (fun t : ℝ ↦ lineMap a b t - z₀) (Icc (0 : ℝ) 1) := by fun_prop
  have h3 : ContinuousOn (fun t : ℝ ↦ (lineMap a b t - z₀) ^ k) (Icc (0 : ℝ) 1) := h2.pow k
  have h4 : ContinuousOn (fun t : ℝ ↦ φ (lineMap a b t) * (lineMap a b t - z₀) ^ k)
      (Icc (0 : ℝ) 1) := h1.mul h3
  have h5 : ContinuousOn (fun _ : ℝ ↦ (b - a)) (Icc (0 : ℝ) 1) := continuousOn_const
  exact ((h4.mul h5).intervalIntegrable_of_Icc zero_le_one)

/-- The sum of the integrands of the Laurent coefficients is integrable. -/
theorem segSum_integrable {φ : ℂ → ℂ} {a b z z₀ : ℂ} (hφ : ContinuousOn φ [a -[ℝ] b]) (N : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ ∑ k ∈ Finset.range (N + 1),
        φ (lineMap a b t) * ((lineMap a b t - z₀) ^ k * (z - z₀)⁻¹ ^ (k + 1)) * (b - a))
      volume 0 1 :=
  ((continuousOn_finsetSum _ fun k _ ↦ continuousOn_segSummand hφ k).intervalIntegrable_of_Icc
    zero_le_one)

/-- **The lecturer's Laurent expansion, pointwise** (lecture 13 p.4): for `w` on the segment and
`z` outside it,

    φ(w)/(w - z)·(b-a) + Σₖ₌₀^N φ(w)(w - z₀)^k (z - z₀)^(-k-1)·(b-a)
        = φ(w)·((w - z₀)(z - z₀)⁻¹)^(N+1)·(w - z)⁻¹·(b-a).
-/
theorem segIntegrand_add_geom_sum {φ : ℂ → ℂ} {a b z z₀ : ℂ} (t : ℝ) (N : ℕ)
    (hz0 : z ≠ z₀) (hwz : lineMap a b t ≠ z) :
    φ (lineMap a b t) * (lineMap a b t - z)⁻¹ * (b - a) +
        ∑ k ∈ Finset.range (N + 1),
          φ (lineMap a b t) * ((lineMap a b t - z₀) ^ k * (z - z₀)⁻¹ ^ (k + 1)) * (b - a) =
      φ (lineMap a b t) *
          (((lineMap a b t - z₀) * (z - z₀)⁻¹) ^ (N + 1) * (lineMap a b t - z)⁻¹) * (b - a) := by
  have key : lineMap a b t - z₀ - (z - z₀) = lineMap a b t - z := by ring
  have h1 : ((lineMap a b t - z₀) * (z - z₀)⁻¹) ^ (N + 1) * (lineMap a b t - z)⁻¹ =
      (lineMap a b t - z)⁻¹ +
        ∑ k ∈ Finset.range (N + 1), (lineMap a b t - z₀) ^ k * (z - z₀)⁻¹ ^ (k + 1) := by
    have hB : (z - z₀) ≠ 0 := sub_ne_zero.mpr hz0
    have hAB : lineMap a b t - z₀ - (z - z₀) ≠ 0 := by
      rw [key]
      exact sub_ne_zero.mpr hwz
    have := invSub_geom_sum_eq (lineMap a b t - z₀) (z - z₀) N hB hAB
    rwa [key] at this
  rw [h1, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]

/-- **The expansion after integrating**: the Cauchy transform of a segment plus the partial sum of
its Laurent expansion at `z₀` is the integral of the (small) remainder term. -/
theorem segIntegral_add_geom_sum {φ : ℂ → ℂ} {a b z z₀ : ℂ} (hφ : ContinuousOn φ [a -[ℝ] b])
    (hz0 : z ≠ z₀) (hz : ∀ t ∈ Icc (0 : ℝ) 1, lineMap a b t ≠ z) (N : ℕ) :
    segIntegral φ a b z +
        ∑ k ∈ Finset.range (N + 1), segCoeff φ a b z₀ k * (z - z₀)⁻¹ ^ (k + 1) =
      ∫ t in (0 : ℝ)..1, φ (lineMap a b t) *
        (((lineMap a b t - z₀) * (z - z₀)⁻¹) ^ (N + 1) * (lineMap a b t - z)⁻¹) * (b - a) := by
  have hI1 : IntervalIntegrable (fun t : ℝ ↦ φ (lineMap a b t) * (lineMap a b t - z)⁻¹ * (b - a))
      volume 0 1 := segIntegral_integrable hφ hz
  have hI2 : IntervalIntegrable (fun t : ℝ ↦ ∑ k ∈ Finset.range (N + 1),
      φ (lineMap a b t) * ((lineMap a b t - z₀) ^ k * (z - z₀)⁻¹ ^ (k + 1)) * (b - a))
      volume 0 1 := segSum_integrable hφ N
  have hI2' : ∀ k ∈ Finset.range (N + 1), IntervalIntegrable
      (fun t : ℝ ↦ φ (lineMap a b t) * ((lineMap a b t - z₀) ^ k * (z - z₀)⁻¹ ^ (k + 1)) * (b - a))
      volume 0 1 := fun k _ ↦
    ((continuousOn_segSummand hφ k).intervalIntegrable_of_Icc zero_le_one)
  -- the sum of the coefficients, integrated term by term
  have hsum : ∑ k ∈ Finset.range (N + 1), segCoeff φ a b z₀ k * (z - z₀)⁻¹ ^ (k + 1) =
      ∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.range (N + 1),
        φ (lineMap a b t) * ((lineMap a b t - z₀) ^ k * (z - z₀)⁻¹ ^ (k + 1)) * (b - a) := by
    rw [intervalIntegral.integral_finsetSum hI2']
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have h2 : segCoeff φ a b z₀ k * (z - z₀)⁻¹ ^ (k + 1) =
        (∫ t in (0 : ℝ)..1, φ (lineMap a b t) * (lineMap a b t - z₀) ^ k * (b - a)) *
          (z - z₀)⁻¹ ^ (k + 1) :=
      rfl
    rw [h2, ← intervalIntegral.integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t _ ↦ ?_)
    ring
  have hstep :
      (∫ t in (0 : ℝ)..1, φ (lineMap a b t) * (lineMap a b t - z)⁻¹ * (b - a)) +
          ∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.range (N + 1),
            φ (lineMap a b t) * ((lineMap a b t - z₀) ^ k * (z - z₀)⁻¹ ^ (k + 1)) * (b - a) =
        ∫ t in (0 : ℝ)..1, φ (lineMap a b t) *
          (((lineMap a b t - z₀) * (z - z₀)⁻¹) ^ (N + 1) * (lineMap a b t - z)⁻¹) * (b - a) := by
    rw [← intervalIntegral.integral_add hI1 hI2]
    refine integral_congr_ae'
      (Filter.Eventually.of_forall fun x hx ↦
        segIntegrand_add_geom_sum x N hz0 (hz x (mem_Icc.mpr ⟨hx.1.le, hx.2⟩)))
      (Filter.Eventually.of_forall fun x hx ↦ by
        have h1 : (1 : ℝ) < x := hx.1
        have h2 : x ≤ (0 : ℝ) := hx.2
        exact absurd h1 (by linarith))
  have hA : segIntegral φ a b z +
      ∑ k ∈ Finset.range (N + 1), segCoeff φ a b z₀ k * (z - z₀)⁻¹ ^ (k + 1) =
      (∫ t in (0 : ℝ)..1, φ (lineMap a b t) * (lineMap a b t - z)⁻¹ * (b - a)) +
          ∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.range (N + 1),
            φ (lineMap a b t) * ((lineMap a b t - z₀) ^ k * (z - z₀)⁻¹ ^ (k + 1)) * (b - a) := by
    rw [hsum]
    rw [show (∫ t in (0 : ℝ)..1, φ (lineMap a b t) * (lineMap a b t - z)⁻¹ * (b - a)) =
      segIntegral φ a b z from rfl]
  exact hA.trans hstep

/-! ## Approximability -/

/-- **The lecturer's estimate for the Cauchy transform of a segment** (lecture 13 p.4).  If the
segment is at distance `≥ ρ > r` from `K` in the sense that `‖γ(t) - z₀‖ ≤ r < ρ < ‖z - z₀‖` on the
segment and `φ` is bounded on the segment by `M`, then the Cauchy transform differs from the partial
sum of its Laurent expansion at `z₀` by at most `(r/ρ)^(N+1) · M‖b - a‖/(ρ - r)`, which tends to
`0`. -/
theorem norm_segIntegral_add_geom_sum_le {φ : ℂ → ℂ} {a b z z₀ : ℂ} {r ρ M : ℝ} (N : ℕ)
    (hφ : ContinuousOn φ [a -[ℝ] b]) (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖φ (lineMap a b t)‖ ≤ M)
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, ‖lineMap a b t - z₀‖ ≤ r) (hr0 : 0 ≤ r) (hrρ : r < ρ)
    (hz : ρ < ‖z - z₀‖) :
    ‖segIntegral φ a b z +
        ∑ k ∈ Finset.range (N + 1), segCoeff φ a b z₀ k * (z - z₀)⁻¹ ^ (k + 1)‖ ≤
      (r / ρ) ^ (N + 1) * (M * ‖b - a‖ / (ρ - r)) := by
  have hz0 : z ≠ z₀ := fun h ↦ by
    rw [h, sub_self, norm_zero] at hz
    linarith
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, lineMap a b t ≠ z := by
    intro t ht hEq
    have h1 := hr t ht
    rw [hEq] at h1
    linarith
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_refl 0, zero_le_one⟩)
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖φ (lineMap a b t) * (((lineMap a b t - z₀) * (z - z₀)⁻¹) ^ (N + 1) *
        (lineMap a b t - z)⁻¹) * (b - a)‖ ≤ M * ((r / ρ) ^ (N + 1) / (ρ - r)) * ‖b - a‖ := by
    intro t ht
    have h1 := hM t ht
    have h2 := norm_geom_sum_le (lineMap a b t) z z₀ hr0 (hr t ht) hrρ hz N
    calc ‖φ (lineMap a b t) * (((lineMap a b t - z₀) * (z - z₀)⁻¹) ^ (N + 1) *
          (lineMap a b t - z)⁻¹) * (b - a)‖
        = ‖φ (lineMap a b t)‖ * ‖((lineMap a b t - z₀) * (z - z₀)⁻¹) ^ (N + 1) *
            (lineMap a b t - z)⁻¹‖ * ‖b - a‖ := by rw [norm_mul, norm_mul]
      _ ≤ M * ((r / ρ) ^ (N + 1) / (ρ - r)) * ‖b - a‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) hM0) (norm_nonneg _)
  calc ‖segIntegral φ a b z +
        ∑ k ∈ Finset.range (N + 1), segCoeff φ a b z₀ k * (z - z₀)⁻¹ ^ (k + 1)‖
      = ‖∫ t in (0 : ℝ)..1, φ (lineMap a b t) *
          (((lineMap a b t - z₀) * (z - z₀)⁻¹) ^ (N + 1) * (lineMap a b t - z)⁻¹) * (b - a)‖ :=
        by rw [segIntegral_add_geom_sum hφ hz0 hne N]
    _ ≤ M * ((r / ρ) ^ (N + 1) / (ρ - r)) * ‖b - a‖ := norm_integral_le_of_forall_norm_le hbound
    _ = (r / ρ) ^ (N + 1) * (M * ‖b - a‖ / (ρ - r)) := by ring

/-- The lecturer's partial sums belong to `PoleAt q K`: they are rational functions on `K` whose
only pole is at `q` (of order at most `N+1`). -/
theorem mem_PoleAt_segApprox (N : ℕ) (c : ℕ → ℂ) (q : ℂ) :
    (fun z : ↥K ↦ ∑ k ∈ Finset.range (N + 1), c k * invSub q K z ^ (k + 1)) ∈ PoleAt q K :=
  mem_PoleAt_sum _ c (fun k ↦ k + 1) q

/-- **The heart of the lecturer's proof of the weak Runge theorem** (lecture 13 p.3–4).  Let
`[a,b]` be a line segment and `z₀` a point such that the segment stays in `B̄(z₀; r)` while `K`
stays outside `B(z₀; ρ)`, with `r < ρ`.  Then the Cauchy transform of any function that is
continuous on the segment, restricted to `K`, is a uniform limit on `K` of rational functions with
a single pole at `z₀` — the lecturer's "Laurent expansion about `z₀`, converging normally on `K`,
whose partial sums have a pole at `z₀ ∈ ℂ∞ − K`".

The condition `[a,b] ⊆ B̄(z₀;r)` and `K ⊆ ℂ − B̄(z₀;ρ)` is exactly what the lecturer arranges by
subdividing the polygons of the Separation Lemma into pieces of length `< δ = d(K,E)` and taking
`z₀` to be the midpoint of a piece: then `B̄(z₀; δ/2) ∩ K = ∅`. -/
theorem approximable_segIntegral {φ : ℂ → ℂ} {a b z₀ : ℂ} {r ρ : ℝ}
    (hφ : ContinuousOn φ [a -[ℝ] b]) (hr0 : 0 ≤ r)
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, ‖lineMap a b t - z₀‖ ≤ r) (hrρ : r < ρ)
    (hK : ∀ z ∈ K, ρ < ‖(z : ℂ) - z₀‖) :
    Approximable (PoleAt z₀ K) fun z : ↥K ↦ segIntegral φ a b z := by
  obtain ⟨M, hM⟩ := exists_norm_le_of_continuousOn hφ
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hq0 : 0 ≤ r / ρ := div_nonneg hr0 hρ0.le
  have hq1 : r / ρ < 1 := (div_lt_one hρ0).mpr hrρ
  intro ε ε0
  obtain ⟨N, hN⟩ := exists_pow_mul_lt (C := M * ‖b - a‖ / (ρ - r)) hq0 hq1 ε0
  have hbound : ∀ (z : ℂ), ρ < ‖z - z₀‖ →
      ‖segIntegral φ a b z +
          ∑ k ∈ Finset.range (N + 1), segCoeff φ a b z₀ k * (z - z₀)⁻¹ ^ (k + 1)‖ ≤
        (r / ρ) ^ (N + 1) * (M * ‖b - a‖ / (ρ - r)) := fun z hz ↦
    norm_segIntegral_add_geom_sum_le N hφ hM hr hr0 hrρ hz
  refine ⟨segApprox K φ a b z₀ N, ?_, fun z ↦ ?_⟩
  · exact mem_PoleAt_segApprox N (fun k ↦ -(segCoeff φ a b z₀ k)) z₀
  · have hz : ρ < ‖(z : ℂ) - z₀‖ := hK z z.2
    have h1 : ‖segIntegral φ a b z +
        ∑ k ∈ Finset.range (N + 1), segCoeff φ a b z₀ k * ((z : ℂ) - z₀)⁻¹ ^ (k + 1)‖ ≤
        (r / ρ) ^ (N + 1) * (M * ‖b - a‖ / (ρ - r)) := hbound z hz
    have hRz : segApprox K φ a b z₀ N z =
        -∑ k ∈ Finset.range (N + 1), segCoeff φ a b z₀ k * ((z : ℂ) - z₀)⁻¹ ^ (k + 1) := by
      simp only [segApprox, invSub, neg_mul, Finset.sum_neg_distrib]
    have h3 : (r / ρ : ℝ) ^ (N + 1) * (M * ‖b - a‖ / (ρ - r)) < ε := hN (N + 1) (Nat.le_succ N)
    calc ‖(fun z : ↥K ↦ segIntegral φ a b z) z - segApprox K φ a b z₀ N z‖
        = ‖segIntegral φ a b z +
            ∑ k ∈ Finset.range (N + 1), segCoeff φ a b z₀ k * ((z : ℂ) - z₀)⁻¹ ^ (k + 1)‖ := by
          rw [hRz, sub_neg_eq_add]
      _ ≤ (r / ρ) ^ (N + 1) * (M * ‖b - a‖ / (ρ - r)) := h1
      _ < ε := h3

end

end Conway

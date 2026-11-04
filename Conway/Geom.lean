/-
Copyright (c) 2026 MA5217 formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MA5217 formalization project (Conway, Chapter VIII)
-/

module

public import Conway.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# MA5217 / Conway Chapter VIII, §1: the geometric series behind the Laurent expansion

This is the elementary algebra and estimates behind the lecturer's Laurent expansion (lecture 13
p.3–4): expanding `(w - z)⁻¹` in powers of `(z - z₀)⁻¹`,

    (w - z)⁻¹ = -Σₖ₌₀^N (w - z₀)^k (z - z₀)^(-k-1) + ((w - z₀)/(z - z₀))^(N+1) (w - z)⁻¹,

together with the estimate `‖((w - z₀)(z - z₀)⁻¹)^(N+1) (w - z)⁻¹‖ ≤ (r/ρ)^(N+1)/(ρ - r)` on
`‖w - z₀‖ ≤ r < ρ < ‖z - z₀‖` ("normally convergent", lecture 13 p.4).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Conway

noncomputable section

/-! ## The geometric series in the form `1/(w - z) = -Σₖ (w - z₀)^k (z - z₀)^(-k-1)` -/

/-- The partial sums of the geometric series `Σₖ A^k (B⁻¹)^(k+1)`, in the form needed to expand
`(w - z)⁻¹` about `z₀` (with `A = w - z₀`, `B = z - z₀`, so that `A - B = w - z`). -/
theorem invSub_geom_sum (A B : ℂ) (N : ℕ) (hB : B ≠ 0) (hAB : A - B ≠ 0) :
    (A - B)⁻¹ + ∑ k ∈ Finset.range (N + 1), A ^ k * (B⁻¹) ^ (k + 1) =
      (A * B⁻¹) ^ (N + 1) * (A - B)⁻¹ := by
  have hsum : ∑ k ∈ Finset.range (N + 1), A ^ k * (B⁻¹) ^ (k + 1) =
      B⁻¹ * ∑ k ∈ Finset.range (N + 1), (A * B⁻¹) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    calc A ^ k * (B⁻¹) ^ (k + 1) = A ^ k * (B⁻¹ ^ k * B⁻¹) := by rw [pow_succ]
      _ = A ^ k * B⁻¹ ^ k * B⁻¹ := by rw [mul_assoc]
      _ = (A * B⁻¹) ^ k * B⁻¹ := by rw [← mul_pow]
      _ = B⁻¹ * (A * B⁻¹) ^ k := by rw [mul_comm _ B⁻¹]
  have h2 : (A - B) * B⁻¹ = A * B⁻¹ - 1 := by
    rw [sub_mul, mul_inv_cancel₀ hB]
  have hS : (1 - A * B⁻¹) * ∑ k ∈ Finset.range (N + 1), (A * B⁻¹) ^ k =
      1 - (A * B⁻¹) ^ (N + 1) := by
    rw [mul_comm, geom_sum_mul_neg]
  have h3 : (A - B) * ((A * B⁻¹) ^ (N + 1) * (A - B)⁻¹) = (A * B⁻¹) ^ (N + 1) := by
    rw [mul_comm _ (A - B)⁻¹, ← mul_assoc, mul_inv_cancel₀ hAB, one_mul]
  apply (mul_right_inj' hAB).mp
  rw [mul_add, mul_inv_cancel₀ hAB, hsum, ← mul_assoc, h2, h3]
  have h4 : (A * B⁻¹ - 1) * ∑ k ∈ Finset.range (N + 1), (A * B⁻¹) ^ k =
      -((1 - A * B⁻¹) * ∑ k ∈ Finset.range (N + 1), (A * B⁻¹) ^ k) := by ring
  rw [h4, hS]
  ring

/-- The expansion itself: `(w - z)⁻¹ = Σₖ₌₀^N (w - z₀)^k (z - z₀)^(-k-1) + (small remainder)`,
i.e. the Laurent expansion of `w ↦ (w - z)⁻¹` in powers of `(z - z₀)⁻¹`, written the other way
round. -/
theorem invSub_geom_sum_eq (A B : ℂ) (N : ℕ) (hB : B ≠ 0) (hAB : A - B ≠ 0) :
    (A * B⁻¹) ^ (N + 1) * (A - B)⁻¹ =
      (A - B)⁻¹ + ∑ k ∈ Finset.range (N + 1), A ^ k * (B⁻¹) ^ (k + 1) :=
  (invSub_geom_sum A B N hB hAB).symm

/-- The remainder `‖(A - B)⁻¹ + Σₖ A^k (B⁻¹)^(k+1)‖ ≤ (r/ρ)^(N+1)/(ρ - r)` of the geometric
expansion, in terms of the bounds `‖A‖ ≤ r < ρ ≤ ‖B‖`. -/
theorem norm_invSub_add_geom_sum_le {A B : ℂ} {r ρ : ℝ} (hr0 : 0 ≤ r) (hA : ‖A‖ ≤ r)
    (hAρ : r < ρ) (hB : ρ < ‖B‖) (N : ℕ) :
    ‖(A - B)⁻¹ + ∑ k ∈ Finset.range (N + 1), A ^ k * (B⁻¹) ^ (k + 1)‖ ≤
      (r / ρ) ^ (N + 1) / (ρ - r) := by
  have hρ0 : (0 : ℝ) < ρ := by linarith [norm_nonneg A]
  have hB0 : (0 : ℝ) < ‖B‖ := by linarith [norm_nonneg B]
  have hBz : B ≠ 0 := fun h ↦ by rw [h, norm_zero] at hB; linarith
  have hAB0 : A - B ≠ 0 := fun h ↦ by
    have h1 : A = B := sub_eq_zero.mp h
    rw [h1] at hA
    linarith
  have hnorm : ‖A * B⁻¹‖ ≤ r / ρ := by
    rw [norm_mul, norm_inv, div_eq_mul_inv]
    refine mul_le_mul hA ?_ (inv_nonneg.mpr (le_of_lt hB0)) hr0
    exact (inv_le_inv₀ hB0 hρ0).mpr (le_of_lt hB)
  have hAB2 : ρ - r ≤ ‖A - B‖ := by
    have h1 : ‖B‖ ≤ ‖B - A‖ + ‖A‖ := by
      have h2 : ‖B - A + A‖ ≤ ‖B - A‖ + ‖A‖ := norm_add_le _ _
      rwa [sub_add_cancel] at h2
    have h2 : ‖B - A‖ = ‖A - B‖ := norm_sub_rev _ _
    linarith
  calc ‖(A - B)⁻¹ + ∑ k ∈ Finset.range (N + 1), A ^ k * (B⁻¹) ^ (k + 1)‖
      = ‖(A * B⁻¹) ^ (N + 1) * (A - B)⁻¹‖ := by rw [invSub_geom_sum A B N hBz hAB0]
    _ = ‖A * B⁻¹‖ ^ (N + 1) * ‖A - B‖⁻¹ := by rw [norm_mul, norm_pow, norm_inv]
    _ ≤ (r / ρ) ^ (N + 1) / (ρ - r) := by
        rw [div_eq_mul_inv]
        refine mul_le_mul ?_ ?_ ?_ ?_
        · exact pow_le_pow_left₀ (norm_nonneg _) hnorm _
        · exact inv_le_inv₀ (norm_pos_iff.mpr hAB0) (by linarith) |>.mpr hAB2
        · exact inv_nonneg.mpr (by linarith)
        · positivity

/-- **The lecturer's estimate** (lecture 13 p.4, "normally convergent"): the tail of the Laurent
expansion of `w ↦ (w - z)⁻¹` about `z₀` is bounded by a geometric term on `‖w - z₀‖ ≤ r < ρ <
‖z - z₀‖`. -/
theorem norm_geom_sum_le (w z z₀ : ℂ) {r ρ : ℝ} (hr0 : 0 ≤ r) (hw : ‖w - z₀‖ ≤ r)
    (hrρ : r < ρ) (hz : ρ < ‖z - z₀‖) (N : ℕ) :
    ‖((w - z₀) * (z - z₀)⁻¹) ^ (N + 1) * (w - z)⁻¹‖ ≤ (r / ρ) ^ (N + 1) / (ρ - r) := by
  have key : w - z₀ - (z - z₀) = w - z := by ring
  have hz0 : z - z₀ ≠ 0 := fun h ↦ by
    have h1 : z = z₀ := sub_eq_zero.mp h
    rw [h1, sub_self, norm_zero] at hz
    linarith
  have hwz : w ≠ z := fun h ↦ by
    rw [h] at hw
    linarith
  have hAB : w - z₀ - (z - z₀) ≠ 0 := by
    rw [key]
    exact sub_ne_zero.mpr hwz
  have h := norm_invSub_add_geom_sum_le hr0 hw hrρ hz N
  rw [invSub_geom_sum (w - z₀) (z - z₀) N hz0 hAB, key] at h
  exact h

/-- The geometric term `q ^ n * C` becomes smaller than any prescribed `ε`. -/
theorem exists_pow_mul_lt {q C ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (ε0 : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, q ^ n * C < ε := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const C
  rw [zero_mul] at h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h.eventually (isOpen_Iio.mem_nhds ε0))
  exact ⟨N, fun n hn ↦ hN n hn⟩

/-! ## The Taylor expansion behind the case `w = ∞` of the pole pushing lemma

This is the same computation as `Conway.invSub_geom_sum`, this time with `A = z - a` and
`B = z₀ - a`, so that `A - B = z - z₀`:

    (z - z₀)⁻¹ = Σₖ₌₀^N (z - a)^k (z₀ - a)^(-k-1) + ((z - a) / (z₀ - a))^(N+1) (z - z₀)⁻¹.

The partial sums are *polynomials* in `z`.  This is the identity behind the lecturer's treatment of
the case `w = ∞` (lecture 14 p.3): choose `a ∈ ℂ` and `R > 0` with `K ⊆ B(a;R)` and
`z₀ ∉ B(a;R)`; then those polynomials converge uniformly to `z ↦ (z - z₀)⁻¹` on `K`. -/

/-- The Taylor remainder estimate: `‖((z - a) * (z₀ - a)⁻¹)^(N+1) * (z - z₀)⁻¹‖ ≤
(R / ρ)^(N+1) * (ρ - R)⁻¹` on `‖z - a‖ ≤ R < ρ ≤ ‖z₀ - a‖`.  Compare
`Conway.norm_geom_sum_le`, which is the same estimate for the Laurent expansion. -/
theorem norm_taylor_geom_sum_le {z z₀ a : ℂ} {R ρ : ℝ} (hR0 : 0 ≤ R) (hz : ‖z - a‖ ≤ R)
    (hRρ : R < ρ) (hρ : ρ ≤ ‖z₀ - a‖) (N : ℕ) :
    ‖((z - a) * (z₀ - a)⁻¹) ^ (N + 1) * (z - z₀)⁻¹‖ ≤ (R / ρ) ^ (N + 1) * (ρ - R)⁻¹ := by
  have hρ0 : (0 : ℝ) < ρ := by linarith [norm_nonneg (z₀ - a)]
  have hB : z₀ - a ≠ 0 := fun h ↦ by rw [h, norm_zero] at hρ; linarith
  have hsum : ‖z₀ - a‖ ≤ ‖z₀ - z‖ + ‖z - a‖ := by
    have h4 : z₀ - a = z₀ - z + (z - a) := by ring
    rw [h4]
    exact norm_add_le _ _
  have hzB : z - z₀ ≠ 0 := fun h ↦ by
    have hz0 : z = z₀ := sub_eq_zero.mp h
    have h2 : ‖z₀ - a‖ ≤ R := by rw [← hz0]; exact hz
    linarith
  have hq : ‖(z - a) * (z₀ - a)⁻¹‖ ≤ R / ρ := by
    rw [norm_mul, norm_inv, div_eq_mul_inv]
    gcongr
  have h1 : ‖((z - a) * (z₀ - a)⁻¹) ^ (N + 1)‖ ≤ (R / ρ) ^ (N + 1) := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hq _
  have h5 : ρ - R ≤ ‖z - z₀‖ := by
    have h6 : ‖z₀ - z‖ = ‖z - z₀‖ := norm_sub_rev _ _
    linarith
  have h2 : ‖(z - z₀)⁻¹‖ ≤ (ρ - R)⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (norm_pos_iff.mpr hzB) (by linarith)).mpr h5
  calc ‖((z - a) * (z₀ - a)⁻¹) ^ (N + 1) * (z - z₀)⁻¹‖
      = ‖((z - a) * (z₀ - a)⁻¹) ^ (N + 1)‖ * ‖(z - z₀)⁻¹‖ := norm_mul _ _
    _ ≤ (R / ρ) ^ (N + 1) * (ρ - R)⁻¹ := by gcongr

end

end Conway

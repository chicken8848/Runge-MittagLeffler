/-
Copyright (c) 2026 MA5217 formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MA5217 formalization project (Conway, Chapter VIII)
-/

module

public import Conway.Main
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.Complex.SummableUniformlyOn
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The partial fraction expansion of `π · cot (π ·)` (Conway VIII.5.3, lecture 16)

This is the lecturer's own proof (lecture 16 p.5-7), which is deliberately elementary: everything
is done with the Weierstrass M-test and ordinary limits, not with Mathlib's Euler product for
`sin`.

The series is the lecturer's `g`, split into the summands
`cotTerm n z = 1 / (z - n) + n⁻¹`, so that `cotTerm n z = z / ((z - n) * n) = O (n⁻²)`; the M-test
estimate `Conway.cotTerm_bound` is the only estimate needed and it gives normal convergence on
every closed disc, hence:

* (a) `g` is holomorphic on `ℂ − ℤ` (`Conway.differentiableOn_cotSeries`);
* (b) `g` has residue `1` at every integer (`Conway.tendsto_mul_cotSeries`);
* (c) `g` is odd (`Conway.cotSeries_neg`);
* (d) `g` satisfies the duplication formula (`Conway.cotSeries_dup`);
* the uniqueness proposition (lecture 16 p.7): `g = π · cot (π ·)`, by the removable singularity
  theorem plus Herglotz' lemma (`Conway.cotSeries_eq_cot_pi`);
* the differentiated expansion `π² · sin (π z)⁻¹² = Σ (z - n)⁻¹²`
  (`Conway.pi_sq_div_sin_sq`), where the summand is the term by term derivative of `cotTerm` and
  not the `1 / (z² - n²)` written in the notes (see the doc-string of that theorem).

Because the summands are only conditionally summable when the constants `n⁻¹` are split off, all
limits of symmetric partial sums are taken with `SummationFilter.symmetricIcc`.
-/

open Set Filter Topology Metric Complex
open scoped BigOperators

@[expose] public section

noncomputable section

namespace Conway

/-- The `n`-th summand in the partial fraction expansion of `π · cot (π ·)`. -/
def cotTerm (n : ℤ) (z : ℂ) : ℂ := 1 / (z - n) + (n : ℂ)⁻¹

/-- The function `g` of lecture 16: the series `Σ {1/(z-n) + 1/n : n ∈ ℤ}`. -/
def cotSeries (z : ℂ) : ℂ := ∑' n : ℤ, cotTerm n z

local notation "ℂ_ℤ" => Complex.integerComplement

@[simp]
theorem cotTerm_zero_apply (z : ℂ) : cotTerm 0 z = 1 / z := by
  simp [cotTerm]

theorem cotTerm_eq (n : ℤ) (z : ℂ) (hn : n ≠ 0) (hz : z ≠ n) :
    cotTerm n z = z / ((z - n) * n) := by
  have h1 : (z - n : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  have h2 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [cotTerm]
  field_simp [h1, h2]
  ring

/-- **The M-test estimate** of lecture 16. -/
theorem cotTerm_bound (r : ℝ) (n : ℤ) (z : ℂ) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hn : (2 * r + 1 : ℝ) < ‖(n : ℂ)‖) :
    ‖cotTerm n z‖ ≤ (4 * r) * ((‖(n : ℂ)‖ : ℝ)⁻¹ ^ 2) := by
  have hne : (z : ℂ) ≠ n := by
    intro h
    have : ‖(n : ℂ)‖ ≤ r := by
      rw [← h]
      exact hz
    linarith
  have hn0 : (n : ℤ) ≠ 0 := by
    intro h
    rw [h] at hn
    norm_num at hn
    linarith [show (0 : ℝ) ≤ r from hr]
  have hu : (0 : ℝ) < ‖(n : ℂ)‖ := norm_pos_iff.mpr (by exact_mod_cast hn0)
  have hv : (0 : ℝ) < ‖(z : ℂ) - n‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have h1 : ‖cotTerm n z‖ = ‖(z : ℂ)‖ / (‖(z : ℂ) - n‖ * ‖(n : ℂ)‖) := by
    rw [cotTerm_eq n z hn0 hne, norm_div, norm_mul]
  have h2 : ‖(n : ℂ)‖ - r ≤ ‖(z : ℂ) - n‖ := by
    have := norm_sub_norm_le (n : ℂ) z
    rw [norm_sub_rev] at this
    linarith [hz]
  have hur : (0 : ℝ) < ‖(n : ℂ)‖ - r := by linarith
  have hmul : (0 : ℝ) < ‖(z : ℂ) - n‖ * ‖(n : ℂ)‖ := mul_pos hv hu
  have hmul2 : (0 : ℝ) < (‖(n : ℂ)‖ - r) * ‖(n : ℂ)‖ := mul_pos hur hu
  have hmul3 : (0 : ℝ) < (‖(n : ℂ)‖ - r) * (‖(n : ℂ)‖ - r) := mul_pos hur hur
  have hA : ‖cotTerm n z‖ ≤ r / (‖(z : ℂ) - n‖ * ‖(n : ℂ)‖) := by
    rw [h1]
    gcongr
  have hB : r / (‖(z : ℂ) - n‖ * ‖(n : ℂ)‖) ≤ r / ((‖(n : ℂ)‖ - r) * ‖(n : ℂ)‖) := by
    refine (div_le_div_iff₀ hmul hmul2).mpr ?_
    have h6 : (0 : ℝ) ≤ ‖(z : ℂ) - n‖ - (‖(n : ℂ)‖ - r) := by linarith
    have h7 : (0 : ℝ) ≤ r * ‖(n : ℂ)‖ := mul_nonneg hr hu.le
    nlinarith
  have hC : r / ((‖(n : ℂ)‖ - r) * ‖(n : ℂ)‖) ≤ r / ((‖(n : ℂ)‖ - r) * (‖(n : ℂ)‖ - r)) := by
    refine (div_le_div_iff₀ hmul2 hmul3).mpr ?_
    have h8 : (0 : ℝ) ≤ ‖(n : ℂ)‖ - (‖(n : ℂ)‖ - r) := by linarith
    have h9 : (0 : ℝ) ≤ r * (‖(n : ℂ)‖ - r) := mul_nonneg hr hur.le
    nlinarith
  have hD : r / ((‖(n : ℂ)‖ - r) * (‖(n : ℂ)‖ - r)) = r * ((‖(n : ℂ)‖ - r)⁻¹ ^ 2) := by
    field_simp
  have hE : (‖(n : ℂ)‖ - r)⁻¹ ≤ 2 * ‖(n : ℂ)‖⁻¹ := by
    have h5 : (2 : ℝ) * ‖(n : ℂ)‖⁻¹ = (‖(n : ℂ)‖ / 2)⁻¹ := by field_simp
    rw [h5]
    refine inv_le_inv₀ hur (by linarith) |>.mpr ?_
    linarith
  calc ‖cotTerm n z‖ ≤ r * ((‖(n : ℂ)‖ - r)⁻¹ ^ 2) := hA.trans (hB.trans hC) |>.trans (le_of_eq hD)
    _ ≤ r * ((2 * ‖(n : ℂ)‖⁻¹) ^ 2) := by gcongr
    _ = (4 * r) * ((‖(n : ℂ)‖ : ℝ)⁻¹ ^ 2) := by ring

/-- The summable majorant `4r / n²` of the M-test. -/
theorem summable_cotMajorant (r : ℝ) : Summable fun n : ℤ => (4 * r) * (‖(n : ℂ)‖⁻¹ ^ 2) :=
  Summable.mul_left (4 * r)
    (Summable.congr
      ((Real.summable_one_div_int_pow (p := 2)).2 (by norm_num : (1 : ℕ) < 2)) fun n => by simp)

/-- An integer whose complex norm is bounded by `N` lies in `Icc (-(N:ℤ)) N`. -/
theorem mem_Icc_of_norm_le (N : ℕ) (n : ℤ) (h : ‖(n : ℂ)‖ ≤ (N : ℝ)) :
    n ∈ Finset.Icc (-(N : ℤ)) N := by
  have h1 : ‖(n : ℝ)‖ ≤ (N : ℝ) := by
    refine le_trans ?_ h
    simp
  rw [Real.norm_eq_abs, abs_le] at h1
  rw [Finset.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h2
    have h2' : n < -(N : ℤ) := by omega
    have h3 : (n : ℝ) < -(N : ℝ) := by exact_mod_cast h2'
    linarith [h1.1]
  · by_contra h2
    have h2' : (N : ℤ) < n := by omega
    have h3 : (N : ℝ) < (n : ℝ) := by exact_mod_cast h2'
    linarith [h1.2]

/-- Outside a finite set, the index `n` is far away from every point of a given disc. -/
theorem cot_cofinite_bound (r : ℝ) {n : ℤ}
    (hn : n ∉ Finset.Icc (-(⌈2 * r + 1⌉₊ : ℤ)) ⌈2 * r + 1⌉₊) : (2 * r + 1 : ℝ) < ‖(n : ℂ)‖ := by
  by_contra h
  have h1 : (2 * r + 1 : ℝ) ≤ ⌈2 * r + 1⌉₊ := Nat.le_ceil _
  have h2 : n ∈ Finset.Icc (-(⌈2 * r + 1⌉₊ : ℤ)) ⌈2 * r + 1⌉₊ :=
    mem_Icc_of_norm_le _ n (by
      have h3 : (0 : ℝ) ≤ ‖(n : ℂ)‖ := norm_nonneg _
      linarith)
  exact hn h2

/-- **The M-test** (lecture 16 p.6): the series defining `g` converges normally on every closed
disc. -/
theorem summableUniformlyOn_cotTerm (r : ℝ) :
    SummableUniformlyOn (fun n : ℤ => (fun z : ℂ => cotTerm n z)) (Metric.closedBall 0 r) := by
  have hkey : HasSumUniformlyOn (fun n : ℤ => (fun z : ℂ => cotTerm n z))
      (fun x => ∑' n : ℤ, cotTerm n x) (Metric.closedBall 0 r) := by
    refine HasSumUniformlyOn.of_norm_le_summable_eventually (summable_cotMajorant r) ?_
    filter_upwards
      [Finset.eventually_cofinite_notMem (Finset.Icc (-(⌈2 * r + 1⌉₊ : ℤ)) ⌈2 * r + 1⌉₊)] with n hn
    intro z hz
    have hz' : ‖(z : ℂ)‖ ≤ r := by simpa using hz
    have hr : 0 ≤ r := (norm_nonneg (z : ℂ)).trans hz'
    have h3 : (2 * r + 1 : ℝ) < ‖(n : ℂ)‖ := cot_cofinite_bound r hn
    exact cotTerm_bound r n z hr hz' h3
  exact hkey.summableUniformlyOn

theorem isOpen_integerComplement : IsOpen ℂ_ℤ :=
  Complex.isClosed_range_intCast.isOpen_compl

/-- The series defining `g` converges normally on `ℂ \ ℤ`. -/
theorem summableLocallyUniformlyOn_cotSeries :
    SummableLocallyUniformlyOn (fun n : ℤ => (fun z : ℂ => cotTerm n z)) ℂ_ℤ := by
  refine SummableLocallyUniformlyOn.of_locally_bounded_eventually isOpen_integerComplement ?_
  intro K hK hKc
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mp hKc.isBounded
  set r : ℝ := max R 0 with hrdef
  refine ⟨fun n => (4 * r) * (‖(n : ℂ)‖⁻¹ ^ 2), summable_cotMajorant r, ?_⟩
  filter_upwards
    [Finset.eventually_cofinite_notMem (Finset.Icc (-(⌈2 * r + 1⌉₊ : ℤ)) ⌈2 * r + 1⌉₊)] with n hn
  intro z hz
  have hzr : ‖(z : ℂ)‖ ≤ r := by
    have : dist z 0 ≤ r := (hR hz).trans (le_max_left R 0)
    simpa [hrdef] using this
  have hr : 0 ≤ r := le_max_right R 0
  exact cotTerm_bound r n z hr hzr (cot_cofinite_bound r hn)

/-- Each term `cotTerm n` is differentiable away from its pole. -/
theorem differentiableAt_cotTerm {n : ℤ} {z : ℂ} (hz : z ≠ n) :
    DifferentiableAt ℂ (fun z => cotTerm n z) z := by
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (w : ℂ) - n) z :=
    differentiableAt_id.sub (differentiableAt_const _)
  have h2 : ((fun w : ℂ => (w : ℂ) - n) z) ≠ 0 := by
    intro h
    exact hz (sub_eq_zero.mp h)
  have h4 : DifferentiableAt ℂ (fun w : ℂ => (1 : ℂ) / ((w : ℂ) - n)) z :=
    (differentiableAt_const _).div h1 h2
  exact h4.add (differentiableAt_const _)

/-- **(a) of lecture 16**: `g = cotSeries` is holomorphic on `ℂ − ℤ`. -/
theorem differentiableOn_cotSeries : DifferentiableOn ℂ cotSeries ℂ_ℤ := by
  refine SummableLocallyUniformlyOn.differentiableOn isOpen_integerComplement
    summableLocallyUniformlyOn_cotSeries ?_
  intro n z hz
  refine differentiableAt_cotTerm ?_
  intro h
  exact hz ⟨n, h.symm⟩

/-- The series defining `g` is summable at every point. -/
theorem summable_cotTerm (z : ℂ) : Summable fun n : ℤ => cotTerm n z :=
  (summableUniformlyOn_cotTerm ‖z‖).summable (by simp)

/-- The summands satisfy `cotTerm n (-z) = -cotTerm (-n) z`. -/
theorem cotTerm_neg (n : ℤ) (z : ℂ) : cotTerm n (-z) = -cotTerm (-n) z := by
  have h1 : ((-n : ℤ) : ℂ) = -(n : ℂ) := by
    push_cast
    rfl
  have h2 : (-z - (n : ℂ)) = -(z + (n : ℂ)) := by ring
  have h3 : (z - ((-n : ℤ) : ℂ)) = z + (n : ℂ) := by push_cast; ring
  have hA : (1 : ℂ) / (-z - n) = -(1 / (z + n)) := by
    rw [h2, div_neg]
  have hB : (((-n : ℤ) : ℂ))⁻¹ = -((n : ℂ)⁻¹) := by
    rw [h1, neg_inv]
  change (1 : ℂ) / (-z - n) + (n : ℂ)⁻¹ = -(1 / (z - (-n : ℤ)) + ((-n : ℤ) : ℂ)⁻¹)
  rw [hA, h3, hB, neg_add, neg_neg]

/-- **(c) of lecture 16**: `g` is an odd function. -/
theorem cotSeries_neg (z : ℂ) : cotSeries (-z) = -cotSeries z := by
  have h1 : (fun n : ℤ => cotTerm n (-z)) = (fun n : ℤ => -cotTerm (-n) z) :=
    funext fun n => cotTerm_neg n z
  have h2 : ∑' n : ℤ, cotTerm (-n) z = cotSeries z := by
    simpa [cotSeries] using (tsum_comp_neg (fun n : ℤ => cotTerm n z))
  calc cotSeries (-z) = ∑' n : ℤ, cotTerm n (-z) := rfl
    _ = ∑' n : ℤ, -cotTerm (-n) z := by rw [h1]
    _ = -∑' n : ℤ, cotTerm (-n) z := by rw [tsum_neg (f := fun n : ℤ => cotTerm (-n) z)]
    _ = -cotSeries z := by rw [h2]

/-- `1 ≤ ‖(k : ℂ)‖` for every nonzero integer `k`. -/
theorem one_le_norm_intCast {k : ℤ} (hk : k ≠ 0) : (1 : ℝ) ≤ ‖(k : ℂ)‖ := by
  have h1 : (1 : ℝ) ≤ ‖(k : ℝ)‖ := by
    rw [Real.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hk
  exact le_trans h1 (by simp)

/-- If `m ≠ n` are integers, then `m` does not belong to the closed disc of radius `1 / 2`
centred at `n`. -/
theorem ne_of_mem_closedBall_half {m n : ℤ} (hmn : m ≠ n) {z : ℂ}
    (hz : z ∈ Metric.closedBall (n : ℂ) (1 / 2)) : z ≠ (m : ℂ) := by
  intro h
  have h1 : (1 : ℝ) ≤ ‖(m : ℂ) - n‖ := by
    have := one_le_norm_intCast (k := m - n) (by omega)
    simpa using this
  have h2 : ‖z - n‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hz
  rw [h] at h2
  linarith

/-- Each summand `cotTerm m` is continuous away from its pole. -/
theorem continuousOn_cotTerm {m : ℤ} {s : Set ℂ} (hs : ∀ z ∈ s, (z : ℂ) ≠ m) :
    ContinuousOn (fun z : ℂ => cotTerm m z) s :=
  fun z hz => ((differentiableAt_cotTerm (hs z hz)).continuousAt).continuousWithinAt

/-- The series `g` of lecture 16 with its `n`-th term removed. -/
def cotRest (n : ℤ) (z : ℂ) : ℂ := ∑' m : ℤ, if m = n then 0 else cotTerm m z

theorem continuousOn_cotTerm_ite {n m : ℤ} :
    ContinuousOn (fun z : ℂ => if m = n then (0 : ℂ) else cotTerm m z)
      (Metric.closedBall (n : ℂ) (1 / 2)) := by
  rcases eq_or_ne m n with h | h
  · have h1 : (fun z : ℂ => (if m = n then (0 : ℂ) else cotTerm m z)) = fun _ => (0 : ℂ) := by
      funext z
      exact ite_eq_left h
    rw [h1]
    exact continuousOn_const
  · have h1 : (fun z : ℂ => (if m = n then (0 : ℂ) else cotTerm m z)) =
      (fun z : ℂ => cotTerm m z) := by
      funext z
      exact ite_eq_right h
    rw [h1]
    refine continuousOn_cotTerm ?_
    intro z hz
    exact ne_of_mem_closedBall_half h hz

theorem hasSumUniformlyOn_cotRest (n : ℤ) :
    HasSumUniformlyOn (fun m : ℤ => fun z : ℂ => if m = n then 0 else cotTerm m z)
      (fun z ↦ ∑' m : ℤ, if m = n then 0 else cotTerm m z)
      (Metric.closedBall (n : ℂ) (1 / 2)) := by
  set r : ℝ := ‖(n : ℂ)‖ + 1 with hrdef
  refine HasSumUniformlyOn.of_norm_le_summable_eventually (summable_cotMajorant r) ?_
  filter_upwards [Finset.eventually_cofinite_notMem
      (Finset.Icc (-(⌈(2 : ℝ) * r + 1⌉₊ : ℤ)) ⌈(2 : ℝ) * r + 1⌉₊)] with m hm
  intro z hz
  have hR0 : (0 : ℝ) ≤ r := by rw [hrdef]; positivity
  have hR : ‖(z : ℂ)‖ ≤ r := by
    rw [hrdef]
    have h1 : ‖z - n‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hz
    have h2 : ‖(z : ℂ)‖ ≤ ‖z - n‖ + ‖(n : ℂ)‖ := by
      have h' := norm_add_le (z - n) (n : ℂ)
      rw [sub_add_cancel] at h'
      exact h'
    linarith
  have hbound : (2 * r + 1 : ℝ) < ‖(m : ℂ)‖ := cot_cofinite_bound r hm
  split_ifs with h
  · rw [norm_zero]
    refine mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hR0) ?_
    positivity
  · exact cotTerm_bound r m z hR0 hR hbound

/-- A finite sum of the summands of `cotRest n` is continuous on the closed disc around `n`. -/
theorem continuousOn_cotRest_finset (n : ℤ) (t : Finset ℤ) :
    ContinuousOn (fun z : ℂ => ∑ m ∈ t, (if m = n then (0 : ℂ) else cotTerm m z))
      (Metric.closedBall (n : ℂ) (1 / 2)) :=
  continuousOn_finsetSum t fun _ _ => continuousOn_cotTerm_ite

theorem continuousOn_cotRest (n : ℤ) :
    ContinuousOn (cotRest n) (Metric.closedBall (n : ℂ) (1 / 2)) := by
  have hfreq : ∃ᶠ (t : Finset ℤ) in atTop, ContinuousOn
      (fun z : ℂ => ∑ m ∈ t, (if m = n then (0 : ℂ) else cotTerm m z))
      (Metric.closedBall (n : ℂ) (1 / 2)) :=
    Filter.Frequently.of_forall fun t => continuousOn_cotRest_finset n t
  exact TendstoUniformlyOn.continuousOn (hasSumUniformlyOn_cotRest n).tendstoUniformlyOn hfreq

/-- The value of `g` is the `n`-th term plus the rest of the series. -/
theorem cotRest_eq_sub (n : ℤ) (z : ℂ) : cotRest n z = cotSeries z - cotTerm n z := by
  have h1 : (fun m : ℤ => (if m = n then (0 : ℂ) else cotTerm m z)) =
      (fun m : ℤ => cotTerm m z - if m = n then cotTerm n z else 0) := by
    funext m
    rcases eq_or_ne m n with h | h
    · rw [ite_eq_left h, ite_eq_left h, ← h]
      simp
    · rw [ite_eq_right h, ite_eq_right h]
      simp
  have h2 : HasSum (fun m : ℤ => cotTerm m z - if m = n then cotTerm n z else 0)
      (cotSeries z - cotTerm n z) :=
    ((summable_cotTerm z).hasSum).sub (hasSum_ite_eq n (cotTerm n z))
  have h3 : HasSum (fun m : ℤ => if m = n then (0 : ℂ) else cotTerm m z)
      (cotSeries z - cotTerm n z) := h2.congr_fun (congrFun h1)
  exact h3.tsum_eq

/-- `cotRest n` is continuous at its own pole `n`. -/
theorem continuousAt_cotRest (n : ℤ) : ContinuousAt (cotRest n) (n : ℂ) :=
  (continuousOn_cotRest n).continuousAt
    (closedBall_mem_nhds (n : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))

/-- **(b) of lecture 16**: the function `g = cotSeries` has residue `1` at every integer, i.e.
`(z - n) * g z` tends to `1` as `z` tends to `n` with `z ≠ n`. -/
theorem tendsto_mul_cotSeries (n : ℤ) :
    Tendsto (fun z : ℂ => (z - n) * cotSeries z) (𝓝[≠] (n : ℂ)) (𝓝 1) := by
  have hsub : Tendsto (fun z : ℂ => z - n) (𝓝[≠] (n : ℂ)) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => z - n) (𝓝 (n : ℂ)) (𝓝 ((n : ℂ) - n)) :=
      (continuousAt_id.sub continuousAt_const).tendsto
    simpa using h.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun z : ℂ => (z - n) * cotRest n z) (𝓝[≠] (n : ℂ)) (𝓝 0) := by
    have h := Tendsto.mul hsub
      (((continuousAt_cotRest n).tendsto).mono_left nhdsWithin_le_nhds)
    rw [zero_mul] at h
    exact h
  have h2 : Tendsto (fun z : ℂ => (1 : ℂ) + (z - n) * (n : ℂ)⁻¹) (𝓝[≠] (n : ℂ)) (𝓝 1) := by
    have hc : Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝[≠] (n : ℂ)) (𝓝 1) := tendsto_const_nhds
    have hd : Tendsto (fun _ : ℂ => (n : ℂ)⁻¹) (𝓝[≠] (n : ℂ)) (𝓝 ((n : ℂ)⁻¹)) := tendsto_const_nhds
    have h := Tendsto.add hc (Tendsto.mul hsub hd)
    rw [zero_mul, add_zero] at h
    exact h
  have h3 : Tendsto (fun z : ℂ => (z - n) * cotTerm n z) (𝓝[≠] (n : ℂ)) (𝓝 1) := by
    refine h2.congr' (eventually_nhdsWithin_iff.mpr (Filter.Eventually.of_forall ?_))
    intro z hz
    have hne : (z : ℂ) ≠ n := by simpa using hz
    have h4 : (z : ℂ) - n ≠ 0 := sub_ne_zero.mpr hne
    have hkey : (1 : ℂ) + (z - n) * (n : ℂ)⁻¹ = (z - n) * cotTerm n z := by
      rw [cotTerm]
      field_simp [h4]
    exact hkey
  have h4 : (fun z : ℂ => (z - n) * cotRest n z + (z - n) * cotTerm n z) =
      (fun z : ℂ => (z - n) * cotSeries z) := by
    funext z
    calc (z - n) * cotRest n z + (z - n) * cotTerm n z
        = (z - n) * (cotSeries z - cotTerm n z) + (z - n) * cotTerm n z := by
          rw [cotRest_eq_sub]
      _ = (z - n) * cotSeries z := by ring
  have h5 : Tendsto (fun z : ℂ => (z - n) * cotRest n z + (z - n) * cotTerm n z)
      (𝓝[≠] (n : ℂ)) (𝓝 (0 + 1)) := h1.add h3
  rw [zero_add] at h5
  rw [← h4]
  exact h5

/-! ## The duplication formula for `cot` and Herglotz' lemma -/

/-- Shifting by `π / 2`: this is what makes the duplication formula for `cot` work. -/
theorem sin_shift_pi_div_two (x : ℂ) :
    Complex.sin (x + (Real.pi : ℂ) / 2) = Complex.cos x := by
  rw [Complex.sin_add]
  simp only [Complex.sin_pi_div_two, Complex.cos_pi_div_two, mul_zero, zero_add, mul_one]

/-- Shifting by `π / 2`, the companion of `sin_shift_pi_div_two`. -/
theorem cos_shift_pi_div_two (x : ℂ) :
    Complex.cos (x + (Real.pi : ℂ) / 2) = -Complex.sin x := by
  rw [Complex.cos_add]
  simp only [Complex.sin_pi_div_two, Complex.cos_pi_div_two, mul_zero, mul_one, zero_sub]

/-- **The duplication formula for `cot`** (lecture 16 p.7):
`cot z + cot (z + π/2) = 2 * cot (2 * z)`.

The lecturer only needs the special form `cot (πz) + cot (π(z + 1/2)) = 2 cot (2πz)`, see
`cot_pi_dup`. Both sides are total functions on `ℂ` (`cos x / sin x` is `0` where `sin x = 0`), so
the degenerate cases `sin x = 0` and `cos x = 0` have to be checked by hand: they are exactly the
cases where the addition theorems are applied below with a vanishing denominator. -/
theorem cot_dup (x : ℂ) :
    Complex.cot x + Complex.cot (x + (Real.pi : ℂ) / 2) = 2 * Complex.cot (2 * x) := by
  have h2 : Complex.sin (x + (Real.pi : ℂ) / 2) = Complex.cos x := sin_shift_pi_div_two x
  have h3 : Complex.cos (x + (Real.pi : ℂ) / 2) = -Complex.sin x := cos_shift_pi_div_two x
  rcases eq_or_ne (Complex.sin x) 0 with h1 | h1
  · have h4 : Complex.sin (2 * x) = 0 := by
      rw [Complex.sin_two_mul, h1]
      simp
    rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, h2, h3,
      h4, h1]
    simp
  rcases eq_or_ne (Complex.cos x) 0 with hc | hc
  · have h4 : Complex.sin (2 * x) = 0 := by
      rw [Complex.sin_two_mul, hc]
      simp
    rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, h2, h3,
      h4, hc]
    simp
  have h7 : Complex.sin x ^ 2 + Complex.cos x ^ 2 = 1 := Complex.sin_sq_add_cos_sq x
  have h9 : Complex.cos x ^ 2 - Complex.sin x ^ 2 = 2 * Complex.cos x ^ 2 - 1 := by
    have h9' : Complex.sin x ^ 2 = 1 - Complex.cos x ^ 2 := by
      rw [← h7, add_sub_cancel_right]
    rw [h9']
    ring
  have hA : (2 : ℂ) * ((2 * Complex.cos x ^ 2 - 1) / (2 * Complex.sin x * Complex.cos x)) =
      (2 * Complex.cos x ^ 2 - 1) / (Complex.sin x * Complex.cos x) := by field_simp
  have hB : Complex.cos x / Complex.sin x + (-Complex.sin x) / Complex.cos x =
      (Complex.cos x ^ 2 - Complex.sin x ^ 2) / (Complex.sin x * Complex.cos x) := by
    rw [div_add_div _ _ h1 hc]
    ring_nf
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, h2, h3,
    Complex.sin_two_mul, Complex.cos_two_mul]
  rw [hB, hA, h9]

/-- **The duplication formula** `(d)` of lecture 16 p.7 for `g₀ : z ↦ π · cot (πz)`, in the form
needed by `Conway.exists_eq_const_of_cot_dup`: `g₀ z + g₀ (z + 1/2) = 2 * g₀ (2 * z)`. It is
`cot_dup` applied to `π * z`. -/
theorem cot_pi_dup (z : ℂ) :
    Real.pi * Complex.cot (Real.pi * z) + Real.pi * Complex.cot (Real.pi * (z + 1 / 2)) =
      2 * (Real.pi * Complex.cot (Real.pi * (2 * z))) := by
  have h1 : Real.pi * (z + 1 / 2) = Real.pi * z + Real.pi / 2 := by ring
  have h2 : Real.pi * (2 * z) = 2 * (Real.pi * z) := by ring
  rw [h1, h2, ← mul_add, cot_dup (Real.pi * z)]
  ring

/-- **Herglotz' lemma** (lecture 16 p.7): an entire function `h` with
`2 * h (2 * z) = h z + h (z + 1/2)` for every `z` is constant.

*Deviation from the lecturer's proof.* The lecturer bounds the maximum modulus of `h` on the circle
of radius `2R - 1` by its maximum on the circle of radius `R`, using the strict maximum-modulus
principle. Here we only use that the functional equation expresses `h z` through the two values
`h (z/2)` and `h (z/2 + 1/2)`, which lie closer to the origin: because of the factor `1/2`, a bound
`C` on the disc of radius `R` propagates *with the same constant* `C` to the disc of radius
`2 * R - 1`. Since `R ↦ 2 * R - 1` fixes `1`, starting from the compact disc of radius
`2 = (2 : ℝ) ^ 0 + 1` and iterating over the radii `(2 : ℝ) ^ n + 1` spreads the maximum modulus
over that disc to a global bound, and Liouville's theorem finishes. -/
theorem exists_eq_const_of_cot_dup (h : ℂ → ℂ) (hd : Differentiable ℂ h)
    (hdup : ∀ z : ℂ, (2 : ℂ) * h (2 * z) = h z + h (z + 1 / 2)) :
    ∃ c : ℂ, ∀ z : ℂ, h z = c := by
  have hstep : ∀ (R C : ℝ), (∀ w : ℂ, ‖w‖ ≤ R → ‖h w‖ ≤ C) →
      ∀ z : ℂ, ‖z‖ ≤ 2 * R - 1 → ‖h z‖ ≤ C := by
    intro R C hR z hz
    have h1 : (2 : ℂ) * (z / 2) = z := by field_simp
    have h2 := hdup (z / 2)
    rw [h1] at h2
    have hn2 : ‖(z : ℂ) / 2‖ = ‖(z : ℂ)‖ / 2 := by
      rw [norm_div]
      norm_num
    have hn4 : ‖((1 : ℂ) / 2)‖ = (1 : ℝ) / 2 := by norm_num
    have h3 : ‖(z : ℂ) / 2‖ ≤ R - 1 / 2 := by
      rw [hn2]
      linarith
    have h4' : ‖(z : ℂ) / 2 + (1 : ℂ) / 2‖ ≤ ‖(z : ℂ) / 2‖ + ‖((1 : ℂ) / 2)‖ := norm_add_le _ _
    rw [hn4] at h4'
    have h4 : ‖(z : ℂ) / 2 + (1 : ℂ) / 2‖ ≤ R := by linarith
    have h5 : ‖h (z / 2)‖ ≤ C := hR _ (h3.trans (by linarith))
    have h6 : ‖h (z / 2 + 1 / 2)‖ ≤ C := hR _ h4
    have h7 : ‖(2 : ℂ) * h z‖ ≤ C + C := by
      rw [h2]
      exact (norm_add_le _ _).trans (add_le_add h5 h6)
    have h8 : ‖(2 : ℂ) * h z‖ = 2 * ‖h z‖ := by
      rw [norm_mul]
      norm_num
    linarith
  obtain ⟨w, hw, hmax⟩ :
      ∃ w ∈ Metric.closedBall (0 : ℂ) 2, ∀ y ∈ Metric.closedBall (0 : ℂ) 2, ‖h y‖ ≤ ‖h w‖ := by
    obtain ⟨w, hw, hmax⟩ :=
      (isCompact_closedBall (0 : ℂ) 2).exists_isMaxOn ⟨0, by simp [Metric.mem_closedBall]⟩
        ((hd.continuous.continuousOn).norm)
    exact ⟨w, hw, fun y hy => hmax hy⟩
  have hseed : ∀ y, ‖(y : ℂ)‖ ≤ (2 : ℝ) → ‖h y‖ ≤ ‖h w‖ := by
    intro y hy
    exact hmax y (by simpa [dist_eq_norm] using hy)
  have hbound : ∀ n : ℕ, ∀ z : ℂ, ‖z‖ ≤ (2 : ℝ) ^ n + 1 → ‖h z‖ ≤ ‖h w‖ := by
    intro n
    induction n with
    | zero =>
      intro z hz
      have h2 : ‖(z : ℂ)‖ ≤ (2 : ℝ) := by linarith
      exact hseed z h2
    | succ n ih =>
      intro z hz
      refine hstep ((2 : ℝ) ^ n + 1) ‖h w‖ ih z ?_
      rw [pow_succ] at hz
      linarith
  have hglobal : ∀ z : ℂ, ‖h z‖ ≤ ‖h w‖ := by
    intro z
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(z : ℂ)‖ ≤ (2 : ℝ) ^ n + 1 := by
      obtain ⟨n, hn⟩ := exists_nat_gt (‖(z : ℂ)‖ - 1)
      refine ⟨n, ?_⟩
      have h2 : (n : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast Nat.lt_two_pow_self
      linarith
    exact hbound n z hn
  have hBdd : Bornology.IsBounded (Set.range h) := by
    refine Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mpr
      ⟨‖h w‖, by rintro _ ⟨z, rfl⟩; simpa [dist_eq_norm] using hglobal z⟩
  exact Differentiable.exists_const_forall_eq_of_bounded hd hBdd

/-! ## (d): the duplication formula for `g` (lecture 16 p.6-7)

The lecturer applies the duplication formula of `cot` to the *symmetric* partial sums of the series
defining `g` and then lets `N → ∞`. The calculation with the partial sums is an identity that does
not involve convergence: after pairing the summands with parameters `n` and `-n` (`Conway.cotLayer`)
the two sides differ only by the outermost layer, which leaves one explicit error term
`2 * (2 * z + 2 * N + 1)⁻¹ = O (N⁻¹)`; it vanishes in the limit. -/

/-- The symmetric partial sums of the series defining `g = Conway.cotSeries`. -/
def cotSymSum (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), cotTerm n z

/-- The layer of the series defining `g` that the symmetric partial sums add at step `n`: the two
summands with parameters `n` and `-n`. -/
def cotLayer (n : ℤ) (z : ℂ) : ℂ := cotTerm n z + cotTerm (-n) z

theorem intIcc_insert (a : ℕ) :
    Finset.Icc (-(a + 1) : ℤ) (a + 1) =
      insert (a + 1 : ℤ) (insert (-(a + 1) : ℤ) (Finset.Icc (-a : ℤ) a)) := by
  ext n
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

theorem intIcc_insert_two (a : ℕ) :
    Finset.Icc (-(2 * a + 2) : ℤ) (2 * a + 2) =
      insert (2 * a + 2 : ℤ)
        (insert (-(2 * a + 2) : ℤ)
          (insert (2 * a + 1 : ℤ) (insert (-(2 * a + 1) : ℤ)
            (Finset.Icc (-(2 * a) : ℤ) (2 * a))))) := by
  ext n
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

theorem cotSymSum_zero (z : ℂ) : cotSymSum 0 z = z⁻¹ := by
  simp only [cotSymSum, Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton,
    cotTerm_zero_apply, one_div]

theorem cotSymSum_succ (a : ℕ) (z : ℂ) :
    cotSymSum (a + 1) z = cotLayer (a + 1 : ℤ) z + cotSymSum a z := by
  rw [cotSymSum, cotSymSum]
  push_cast
  rw [intIcc_insert, cotLayer]
  rw [Finset.sum_insert, Finset.sum_insert]
  · abel
  all_goals
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega

theorem cotSymSum_succ_two (a : ℕ) (z : ℂ) :
    cotSymSum (2 * a + 2) z =
      cotLayer (2 * a + 1 : ℤ) z + (cotLayer (2 * a + 2 : ℤ) z + cotSymSum (2 * a) z) := by
  rw [cotSymSum, cotSymSum]
  push_cast
  rw [intIcc_insert_two, cotLayer, cotLayer]
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert]
  · abel
  all_goals
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega

/-- Pairing of the two summands with parameters `n` and `-n`: the constants `n⁻¹` and `(-n)⁻¹`
cancel, which is what makes the duplication formula work. -/
theorem cotTerm_pair (n : ℤ) (z : ℂ) :
    cotTerm n z + cotTerm (-n) z = (z - (n : ℂ))⁻¹ + (z + (n : ℂ))⁻¹ := by
  simp only [cotTerm, one_div, Int.cast_neg]
  ring_nf

theorem cotLayer_eq (n : ℤ) (z : ℂ) : cotLayer n z = (z - (n : ℂ))⁻¹ + (z + (n : ℂ))⁻¹ := by
  rw [cotLayer, cotTerm_pair]

theorem two_mul_inv_two : (2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by norm_num

theorem two_mul_two_add_inv (x c : ℂ) : (2 : ℂ) * (2 * x + c)⁻¹ = (x + c / 2)⁻¹ := by
  have hc2 : (2 : ℂ) * (c / 2) = c := by field_simp
  have h : (2 : ℂ) * x + c = (2 : ℂ) * (x + c / 2) := by
    rw [mul_add, hc2]
  rw [h, mul_inv, ← mul_assoc, two_mul_inv_two, one_mul]

theorem two_mul_two_inv (x : ℂ) : (2 : ℂ) * (2 * x)⁻¹ = x⁻¹ := by
  rw [mul_inv, ← mul_assoc, two_mul_inv_two, one_mul]

/-- One layer at a time of the duplication formula, with the two layers of the doubled sum and a
correction term. -/
theorem cotLayer_dup_step (k : ℤ) (z : ℂ) :
    cotLayer k z + cotLayer k (z + 1 / 2)
      = 2 * (cotLayer (2 * k - 1) (2 * z) + cotLayer (2 * k) (2 * z))
        + (2 * (2 * z + (2 * k + 1))⁻¹ - 2 * (2 * z + (2 * k - 1))⁻¹) := by
  rw [cotLayer_eq k z, cotLayer_eq k (z + 1 / 2), cotLayer_eq (2 * k - 1) (2 * z),
    cotLayer_eq (2 * k) (2 * z)]
  have e1 : ((2 * k - 1 : ℤ) : ℂ) = 2 * (k : ℂ) - 1 := by norm_cast
  have e2 : ((2 * k : ℤ) : ℂ) = 2 * (k : ℂ) := by norm_cast
  rw [e1, e2, mul_add, mul_add, mul_add]
  have h1 : (2 : ℂ) * z - (2 * (k : ℂ) - 1) = 2 * (z - (k : ℂ)) + 1 := by ring
  have h2 : (2 : ℂ) * z + (2 * (k : ℂ) - 1) = 2 * (z + (k : ℂ)) + (-1) := by ring
  have h3 : (2 : ℂ) * z - 2 * (k : ℂ) = 2 * (z - (k : ℂ)) + 0 := by ring
  have h4 : (2 : ℂ) * z + 2 * (k : ℂ) = 2 * (z + (k : ℂ)) + 0 := by ring
  have h5 : (2 : ℂ) * z + (2 * (k : ℂ) + 1) = 2 * (z + (k : ℂ)) + 1 := by ring
  rw [h1, h2, h3, h4, h5]
  rw [two_mul_two_add_inv (z - (k : ℂ)) 1, two_mul_two_add_inv (z + (k : ℂ)) (-1),
    two_mul_two_add_inv (z - (k : ℂ)) 0, two_mul_two_add_inv (z + (k : ℂ)) 0,
    two_mul_two_add_inv (z + (k : ℂ)) 1]
  simp only [zero_div, add_zero]
  have j1 : z + 1 / 2 - (k : ℂ) = (z - (k : ℂ)) + 1 / 2 := by ring
  have j2 : z + 1 / 2 + (k : ℂ) = (z + (k : ℂ)) + 1 / 2 := by ring
  rw [← j1, ← j2]
  abel

/-- **The duplication formula for the symmetric partial sums** (lecture 16 p.6): the error term is
the contribution of the layers `±(2 * a + 1)`, `±(2 * a + 2)` that the doubled sum has twice. -/
theorem cotSymSum_dup (a : ℕ) (z : ℂ) :
    cotSymSum a z + cotSymSum a (z + 1 / 2)
      = 2 * cotSymSum (2 * a) (2 * z) + 2 * (2 * z + (2 * a + 1))⁻¹ := by
  induction a with
  | zero =>
      rw [Nat.mul_zero, cotSymSum_zero, cotSymSum_zero, cotSymSum_zero, Nat.cast_zero, mul_zero,
        zero_add, two_mul_two_inv z, two_mul_two_add_inv z 1]
  | succ a ih =>
      have hL : cotSymSum (a + 1) z + cotSymSum (a + 1) (z + 1 / 2)
          = (cotLayer (a + 1 : ℤ) z + cotLayer (a + 1 : ℤ) (z + 1 / 2))
            + (cotSymSum a z + cotSymSum a (z + 1 / 2)) := by
        rw [cotSymSum_succ, cotSymSum_succ _ (z + 1 / 2)]
        abel
      have hmul : (2 * (a + 1) : ℕ) = 2 * a + 2 := by omega
      have h2b : (2 : ℤ) * (a + 1) - 1 = 2 * a + 1 := by ring
      have h2c : (2 : ℤ) * (a + 1) = 2 * a + 2 := by ring
      have n1 : (2 : ℂ) * ((a : ℂ) + 1) + 1 = 2 * (a : ℂ) + 3 := by ring
      have n2 : (2 : ℂ) * ((a : ℂ) + 1) - 1 = 2 * (a : ℂ) + 1 := by ring
      rw [hL, cotLayer_dup_step ((a : ℤ) + 1), ih, hmul, cotSymSum_succ_two, h2b, h2c]
      push_cast
      rw [n1, n2, mul_add, mul_add, mul_add]
      abel

/-- The symmetric partial sums of the series defining `g` tend to `g`: the symmetric filter is
coarser than the unconditional one, in which the series converges. -/
theorem tendsto_cotSymSum (z : ℂ) :
    Tendsto (fun N : ℕ => cotSymSum N z) atTop (𝓝 (cotSeries z)) := by
  have hsum :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), cotTerm n z) atTop
        (𝓝 (cotSeries z)) := by
    have hle :
        (SummationFilter.symmetricIcc ℤ).filter ≤ (SummationFilter.unconditional ℤ).filter := by
      rw [SummationFilter.unconditional_filter]
      exact SummationFilter.LeAtTop.le_atTop
    have h : HasSum (fun n : ℤ => cotTerm n z) (cotSeries z)
        (SummationFilter.symmetricIcc ℤ) := (summable_cotTerm z).hasSum.mono_left hle
    rw [HasSum, SummationFilter.symmetricIcc_eq_map_Icc_nat, Filter.tendsto_map'_iff] at h
    exact h
  have hfun :
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), cotTerm n z) = fun N => cotSymSum N z :=
    rfl
  rw [hfun] at hsum
  exact hsum

theorem tendsto_double_atTop : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [eventually_ge_atTop (2 * b)] with n hn
  omega

/-- The error term of `Conway.cotSymSum_dup` tends to `0`: it is `O (N⁻¹)`. -/
theorem tendsto_cotSymSum_error (z : ℂ) :
    Tendsto (fun N : ℕ => (2 : ℂ) * (2 * z + (2 * (N : ℂ) + 1))⁻¹) atTop (𝓝 0) := by
  set c := ‖(2 : ℂ) * z + 1‖ with hc
  have hc0 : (0 : ℝ) ≤ c := norm_nonneg _
  have key : ∀ N : ℕ, c + 1 ≤ (N : ℝ) →
      ‖(2 : ℂ) * (2 * z + (2 * (N : ℂ) + 1))⁻¹‖ ≤ (2 : ℝ) * (N : ℝ)⁻¹ := by
    intro N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have h1 : ‖(2 : ℂ) * (N : ℂ)‖ - ‖(-(2 * z + 1) : ℂ)‖ ≤ ‖(2 : ℂ) * (N : ℂ) - -(2 * z + 1)‖ :=
      norm_sub_norm_le _ _
    have h2 : (2 : ℂ) * (N : ℂ) - -(2 * z + 1) = 2 * z + (2 * (N : ℂ) + 1) := by ring
    have h3 : ‖(-(2 * z + 1) : ℂ)‖ = c := by rw [norm_neg, ← hc]
    have hn2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    have h4 : ‖(2 : ℂ) * (N : ℂ)‖ = (2 : ℝ) * (N : ℝ) := by
      rw [norm_mul, hn2, Complex.norm_natCast]
    rw [h2, h3, h4] at h1
    have h5 : (2 : ℝ) * (N : ℝ) - c ≤ ‖2 * z + (2 * (N : ℂ) + 1)‖ := by linarith
    have h6 : (0 : ℝ) < ‖2 * z + (2 * (N : ℂ) + 1)‖ := by linarith
    rw [norm_mul, norm_inv, hn2]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
    rw [inv_le_inv₀ h6 hN0]
    linarith
  have h_ev : ∀ᶠ (N : ℕ) in atTop, c + 1 ≤ (N : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (c + 1))] with N hN
    exact Nat.ceil_le.mp hN
  have h_key :
      ∀ᶠ (N : ℕ) in atTop, ‖(2 : ℂ) * (2 * z + (2 * (N : ℂ) + 1))⁻¹‖ ≤ (2 : ℝ) * (N : ℝ)⁻¹ :=
    h_ev.mono key
  have h_lim : Tendsto (fun N : ℕ => (2 : ℝ) * (N : ℝ)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_natCast_atTop_atTop.inv_tendsto_atTop
    simpa using tendsto_const_nhds.mul h
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => (0 : ℝ))
    (h := fun N : ℕ => (2 : ℝ) * (N : ℝ)⁻¹) tendsto_const_nhds h_lim
      (Eventually.of_forall fun N => norm_nonneg _) h_key

/-- **(d) of lecture 16**: the function `g = Conway.cotSeries` satisfies the duplication formula
`g z + g (z + 1 / 2) = 2 * g (2 * z)` for every `z : ℂ`.

Passing to the limit in `Conway.cotSymSum_dup` leaves only the error term, which vanishes because
`2 * (2 * z + 2 * N + 1)⁻¹ = O (N⁻¹)`. -/
theorem cotSeries_dup (z : ℂ) :
    cotSeries z + cotSeries (z + 1 / 2) = 2 * cotSeries (2 * z) := by
  have h1 : Tendsto (fun N : ℕ => cotSymSum N z + cotSymSum N (z + 1 / 2)) atTop
      (𝓝 (cotSeries z + cotSeries (z + 1 / 2))) :=
    (tendsto_cotSymSum z).add (tendsto_cotSymSum (z + 1 / 2))
  have hsub : Tendsto (fun N : ℕ => cotSymSum (2 * N) (2 * z)) atTop (𝓝 (cotSeries (2 * z))) :=
    (tendsto_cotSymSum (2 * z)).comp tendsto_double_atTop
  have hc : Tendsto (fun _ : ℕ => (2 : ℂ)) atTop (𝓝 2) := tendsto_const_nhds
  have h2 : Tendsto (fun N : ℕ => 2 * cotSymSum (2 * N) (2 * z)) atTop
      (𝓝 (2 * cotSeries (2 * z))) := hc.mul hsub
  have h3 : Tendsto (fun N : ℕ => 2 * cotSymSum (2 * N) (2 * z) +
      (2 : ℂ) * (2 * z + (2 * (N : ℂ) + 1))⁻¹) atTop (𝓝 (2 * cotSeries (2 * z))) := by
    convert h2.add (tendsto_cotSymSum_error z) using 1
    rw [add_zero]
  have h4 : Tendsto (fun N : ℕ => cotSymSum N z + cotSymSum N (z + 1 / 2)) atTop
      (𝓝 (2 * cotSeries (2 * z))) := by
    refine Tendsto.congr' ?_ h3
    filter_upwards [Eventually.of_forall (fun N => cotSymSum_dup N z)] with N hN
    exact hN.symm
  exact tendsto_nhds_unique h1 h4


section Uniq

open scoped Topology

lemma norm_pi : ‖(Real.pi : ℂ)‖ = Real.pi := by
  norm_cast
  rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt Real.pi_pos)]

theorem norm_sq_le_one (x : ℂ) (hx : ‖x‖ ≤ 1) : ‖x‖ ^ 2 ≤ 1 := by
  rw [sq]
  exact ((mul_le_mul_of_nonneg_left hx (norm_nonneg x)).trans_eq (mul_one _)).trans hx

theorem norm_cos_sub_one_le (x : ℂ) (hx : ‖x‖ ≤ 1) : ‖Complex.cos x - 1‖ ≤ ‖x‖ ^ 2 := by
  have h1 : Complex.cos x - 1 = (Complex.cos x - (1 - x ^ 2 / 2)) + ((1 - x ^ 2 / 2) - 1) := by
    ring
  have h2 : ‖((1 : ℂ) - x ^ 2 / 2) - 1‖ ≤ ‖x‖ ^ 2 / 2 := by
    have h3 : ((1 : ℂ) - x ^ 2 / 2) - 1 = -(x ^ 2 / 2) := by ring
    rw [h3, norm_neg]
    have h4 : ‖(x ^ 2 / 2 : ℂ)‖ = ‖x‖ ^ 2 / 2 := by
      rw [norm_div, norm_pow]
      norm_num
    rw [h4]
  have h6 : ‖x‖ ^ 4 ≤ ‖x‖ ^ 2 := by
    have h5 : ‖x‖ ^ 2 ≤ 1 := norm_sq_le_one x hx
    calc ‖x‖ ^ 4 = ‖x‖ ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ ‖x‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
      _ = ‖x‖ ^ 2 := mul_one _
  calc ‖Complex.cos x - 1‖
      = ‖(Complex.cos x - (1 - x ^ 2 / 2)) + ((1 - x ^ 2 / 2) - 1)‖ := congrArg norm h1
    _ ≤ ‖Complex.cos x - (1 - x ^ 2 / 2)‖ + ‖((1 - x ^ 2 / 2) - 1)‖ := norm_add_le _ _
    _ ≤ ‖x‖ ^ 4 * (5 / 96) + ‖x‖ ^ 2 / 2 := add_le_add (Complex.cos_bound hx) h2
    _ ≤ ‖x‖ ^ 2 := by nlinarith [h6]

theorem norm_sin_sub_le (x : ℂ) (hx : ‖x‖ ≤ 1) : ‖Complex.sin x - x‖ ≤ ‖x‖ ^ 3 / 2 := by
  have h1 : Complex.sin x - x = (Complex.sin x - (x - x ^ 3 / 6)) + ((x - x ^ 3 / 6) - x) := by
    ring
  have h2 : ‖((x - x ^ 3 / 6) - x : ℂ)‖ = ‖x‖ ^ 3 / 6 := by
    have h3 : ((x - x ^ 3 / 6) - x : ℂ) = -(x ^ 3 / 6) := by ring
    rw [h3, norm_neg]
    have h4 : ‖(x ^ 3 / 6 : ℂ)‖ = ‖x‖ ^ 3 / 6 := by
      rw [norm_div, norm_pow]
      norm_num
    rw [h4]
  have h3 : ‖x‖ ^ 5 ≤ ‖x‖ ^ 3 := by
    have h4 : ‖x‖ ^ 2 ≤ 1 := norm_sq_le_one x hx
    calc ‖x‖ ^ 5 = ‖x‖ ^ 3 * ‖x‖ ^ 2 := by ring
      _ ≤ ‖x‖ ^ 3 * 1 := mul_le_mul_of_nonneg_left h4 (pow_nonneg (norm_nonneg x) 3)
      _ = ‖x‖ ^ 3 := mul_one _
  have h5 : ‖x‖ ^ 5 / 100 ≤ ‖x‖ ^ 3 / 100 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right h3 ?_
    norm_num
  have h7 : (0 : ℝ) ≤ ‖x‖ ^ 3 := pow_nonneg (norm_nonneg x) 3
  calc ‖Complex.sin x - x‖
      = ‖(Complex.sin x - (x - x ^ 3 / 6)) + ((x - x ^ 3 / 6) - x)‖ := congrArg norm h1
    _ ≤ ‖Complex.sin x - (x - x ^ 3 / 6)‖ + ‖((x - x ^ 3 / 6) - x : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖x‖ ^ 5 / 100 + ‖x‖ ^ 3 / 6 := add_le_add (Complex.sin_bound hx) (le_of_eq h2)
    _ ≤ ‖x‖ ^ 3 / 2 := by nlinarith [h5, h7]

theorem half_norm_le_norm_sin (x : ℂ) (hx : ‖x‖ ≤ 1) : ‖x‖ / 2 ≤ ‖Complex.sin x‖ := by
  have h1 : ‖x‖ ≤ ‖Complex.sin x‖ + ‖Complex.sin x - x‖ := by
    calc ‖x‖ = ‖Complex.sin x + (x - Complex.sin x)‖ := by rw [add_comm, sub_add_cancel]
      _ ≤ ‖Complex.sin x‖ + ‖x - Complex.sin x‖ := norm_add_le _ _
      _ = ‖Complex.sin x‖ + ‖Complex.sin x - x‖ := by rw [norm_sub_rev]
  have h3 : ‖x‖ ^ 3 ≤ ‖x‖ := by
    have h4 : ‖x‖ ^ 2 ≤ 1 := norm_sq_le_one x hx
    calc ‖x‖ ^ 3 = ‖x‖ ^ 2 * ‖x‖ := by ring
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right h4 (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  nlinarith [norm_sin_sub_le x hx, h3]

theorem norm_mul_cos_sub_sin (x : ℂ) (hx : ‖x‖ ≤ 1) :
    ‖x * Complex.cos x - Complex.sin x‖ ≤ 2 * ‖x‖ ^ 3 := by
  have h1 : x * Complex.cos x - Complex.sin x = x * (Complex.cos x - 1) - (Complex.sin x - x) := by
    ring
  have h2 : ‖x * (Complex.cos x - 1)‖ ≤ ‖x‖ ^ 3 := by
    calc ‖x * (Complex.cos x - 1)‖ ≤ ‖x‖ * ‖Complex.cos x - 1‖ := norm_mul_le _ _
      _ ≤ ‖x‖ * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left (norm_cos_sub_one_le x hx) (norm_nonneg x)
      _ = ‖x‖ ^ 3 := by ring
  have h3 : (0 : ℝ) ≤ ‖x‖ ^ 3 := pow_nonneg (norm_nonneg x) 3
  calc ‖x * Complex.cos x - Complex.sin x‖
      = ‖x * (Complex.cos x - 1) - (Complex.sin x - x)‖ := congrArg norm h1
    _ ≤ ‖x * (Complex.cos x - 1)‖ + ‖Complex.sin x - x‖ := norm_sub_le _ _
    _ ≤ ‖x‖ ^ 3 + ‖x‖ ^ 3 / 2 := add_le_add h2 (norm_sin_sub_le x hx)
    _ ≤ 2 * ‖x‖ ^ 3 := by linarith

theorem real_pi_ne_zero : (Real.pi : ℝ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

/-- **The pole cancellation** (lecture 16 p.7): `π · cot (πz) - z⁻¹` is `O ‖z‖` at `z = 0`. -/
theorem norm_pi_cot_sub_inv (w : ℂ) (hw0 : w ≠ 0) (hw : ‖w‖ ≤ Real.pi⁻¹) :
    ‖Real.pi * Complex.cot (Real.pi * w) - w⁻¹‖ ≤ 4 * Real.pi ^ 2 * ‖w‖ := by
  set x : ℂ := Real.pi * w with hx_def
  have hnx : ‖x‖ ≤ 1 := by
    rw [hx_def, norm_mul, norm_pi]
    exact (mul_le_mul_of_nonneg_left hw (le_of_lt Real.pi_pos)).trans_eq (by field_simp)
  have hx0 : x ≠ 0 := by
    rw [hx_def]
    exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hw0
  have hs : Complex.sin x ≠ 0 := by
    intro hsub
    have h' := half_norm_le_norm_sin x hnx
    rw [hsub, norm_zero] at h'
    have h2 : (0 : ℝ) < ‖x‖ / 2 := half_pos (norm_pos_iff.mpr hx0)
    linarith
  have hsu : Complex.sin x * (Complex.sin x)⁻¹ = 1 := mul_inv_cancel₀ hs
  have h1 : x * Complex.cot x - 1 = (x * Complex.cos x - Complex.sin x) / Complex.sin x := by
    have hc : x * Complex.cot x = x * Complex.cos x * (Complex.sin x)⁻¹ := by
      rw [Complex.cot_eq_cos_div_sin, div_eq_mul_inv, ← mul_assoc]
    rw [hc, div_eq_mul_inv, sub_mul, hsu]
  have h2' : (Real.pi * w) * w⁻¹ = Real.pi := by
    rw [mul_assoc, mul_inv_cancel₀ hw0, mul_one]
  have h2 : (Real.pi * w) * Complex.cot (Real.pi * w) * w⁻¹ = Real.pi * Complex.cot (Real.pi * w) :=
    by rw [mul_right_comm, h2']
  have hL : Real.pi * Complex.cot (Real.pi * w) - w⁻¹ = (x * Complex.cot x - 1) * w⁻¹ := by
    rw [sub_mul, hx_def, h2, one_mul]
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  have hmul : ‖x * Complex.cos x - Complex.sin x‖ * ‖Complex.sin x‖⁻¹ ≤
      (2 * ‖x‖ ^ 3) * (‖x‖ / 2)⁻¹ := by
    refine le_trans (mul_le_mul_of_nonneg_right (norm_mul_cos_sub_sin x hnx)
        (inv_nonneg.mpr (norm_nonneg _))) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (inv_le_inv₀ (norm_pos_iff.mpr hs) (half_pos hxpos)).mpr ?_
    exact half_norm_le_norm_sin x hnx
  have h3 : ‖x‖ = Real.pi * ‖w‖ := by rw [hx_def, norm_mul, norm_pi]
  calc ‖Real.pi * Complex.cot (Real.pi * w) - w⁻¹‖
      = ‖(x * Complex.cot x - 1) * w⁻¹‖ := congrArg norm hL
    _ = ‖x * Complex.cot x - 1‖ * ‖w‖⁻¹ := by rw [norm_mul, norm_inv]
    _ = (‖x * Complex.cos x - Complex.sin x‖ * ‖Complex.sin x‖⁻¹) * ‖w‖⁻¹ := by
        rw [h1, norm_div, div_eq_mul_inv]
    _ ≤ ((2 * ‖x‖ ^ 3) * (‖x‖ / 2)⁻¹) * ‖w‖⁻¹ :=
        mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr (norm_nonneg _))
    _ = 4 * Real.pi ^ 2 * ‖w‖ := by
        rw [h3]
        field_simp [hwpos.ne', real_pi_ne_zero]
        ring

end Uniq
section Uniq2

open scoped Topology

/-- `cot` is antiperiodic with period `Real.pi`, with the `1 / 0 = 0` convention. -/
theorem cot_sub_int_mul_pi (k : ℤ) (w : ℂ) :
    Complex.cot (w - (k : ℂ) * Real.pi) = Complex.cot w := by
  rw [← Complex.tan_inv_eq_cot, ← Complex.tan_inv_eq_cot, Complex.tan_periodic.sub_int_mul_eq]

/-- `Complex.cot` vanishes at the origin, by the `1 / 0 = 0` convention. -/
theorem cot_zero : Complex.cot 0 = 0 := by
  rw [Complex.cot_eq_cos_div_sin, Complex.sin_zero, div_zero]

/-- The pole cancellation of lecture 16 p.7, as an estimate near the origin. -/
theorem tendsto_bound :
    ∀ᶠ w : ℂ in 𝓝 0, ‖Real.pi * Complex.cot (Real.pi * w) - w⁻¹‖ ≤
      (4 * Real.pi ^ 2 : ℝ) * ‖w‖ := by
  have key : ∀ w : ℂ, ‖w‖ ≤ Real.pi⁻¹ →
      ‖Real.pi * Complex.cot (Real.pi * w) - w⁻¹‖ ≤ (4 * Real.pi ^ 2 : ℝ) * ‖w‖ := by
    intro w hw
    rcases eq_or_ne w 0 with hw0 | hw0
    · rw [hw0]
      have hz : Real.pi * Complex.cot (Real.pi * (0 : ℂ)) - (0 : ℂ)⁻¹ = 0 := by
        rw [mul_zero, cot_zero, mul_zero, inv_zero, sub_zero]
      rw [hz, norm_zero, mul_zero]
    · exact norm_pi_cot_sub_inv w hw0 hw
  have hpi : (0 : ℝ) < Real.pi⁻¹ := inv_pos.mpr Real.pi_pos
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hpi] with w hw
  refine key w (le_of_lt ?_)
  have hlt : ‖(w : ℂ)‖ < Real.pi⁻¹ := by
    simpa using hw
  exact hlt

/-- The pole cancellation of lecture 16 p.7, in limit form: `π · cot (πw) - w⁻¹ → 0` as `w → 0`. -/
theorem tendsto_pi_cot_sub_inv :
    Filter.Tendsto (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w) - w⁻¹) (𝓝 0) (𝓝 0) := by
  have h1 : Continuous (fun w : ℂ => (4 * Real.pi ^ 2 : ℝ) * ‖w‖) :=
    continuous_const.mul continuous_norm
  have h0 : Filter.Tendsto (fun w : ℂ => (4 * Real.pi ^ 2 : ℝ) * ‖w‖) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa using h1.tendsto (0 : ℂ)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [tendsto_bound, h0.eventually_lt tendsto_const_nhds hε] with w hw1 hw2
  rw [dist_eq, sub_zero]
  exact hw1.trans_lt hw2

/-- The function `z ↦ π · cot (πz) - (z - n)⁻¹` tends to `0` along `z → n`: this is the
cancellation of the two poles at the integer `n` (lecture 16 p.7). -/
theorem tendsto_pi_cot_sub (n : ℤ) :
    Filter.Tendsto (fun z : ℂ => Real.pi * Complex.cot (Real.pi * z) - (z - n)⁻¹) (𝓝 (n : ℂ))
      (𝓝 0) := by
  have hshift : Filter.Tendsto (fun z : ℂ => z - (n : ℂ)) (𝓝 (n : ℂ)) (𝓝 0) := by
    rw [← sub_self (n : ℂ)]
    exact (continuous_id.sub continuous_const).tendsto (n : ℂ)
  have hper : ∀ z : ℂ, Real.pi * Complex.cot (Real.pi * (z - (n : ℂ))) - (z - (n : ℂ))⁻¹ =
      Real.pi * Complex.cot (Real.pi * z) - (z - n)⁻¹ := by
    intro z
    have h2 : Real.pi * (z - (n : ℂ)) = Real.pi * z - (n : ℂ) * Real.pi := by
      rw [mul_sub, mul_comm (n : ℂ) Real.pi]
    rw [h2, ← Complex.tan_inv_eq_cot, ← Complex.tan_inv_eq_cot,
      Complex.tan_periodic.sub_int_mul_eq]
  exact (tendsto_pi_cot_sub_inv.comp hshift).congr hper

/-- The function `z ↦ π · cot (πz) - (z - n)⁻¹` is continuous at the integer `n`: this is the
cancellation of the two poles at `n` (lecture 16 p.7). -/
theorem continuousAt_pi_cot_sub (n : ℤ) :
    ContinuousAt (fun z : ℂ => Real.pi * Complex.cot (Real.pi * z) - (z - n)⁻¹) (n : ℂ) := by
  set F : ℂ → ℂ := fun z : ℂ => Real.pi * Complex.cot (Real.pi * z) - (z - n)⁻¹
  have h1 : Complex.sin ((n : ℂ) * Real.pi) = 0 := Complex.sin_int_mul_pi n
  have h2 : Real.pi * (n : ℂ) = (n : ℂ) * Real.pi := by
    ring
  have hcot : Complex.cot (Real.pi * (n : ℂ)) = 0 := by
    rw [h2, Complex.cot_eq_cos_div_sin, h1, div_zero]
  have h3 : Real.pi * Complex.cot (Real.pi * (n : ℂ)) = 0 := by
    rw [hcot, mul_zero]
  have h4 : ((n : ℂ) - (n : ℂ))⁻¹ = 0 := by
    rw [sub_self, inv_zero]
  have h5 : F (n : ℂ) = Real.pi * Complex.cot (Real.pi * (n : ℂ)) - ((n : ℂ) - (n : ℂ))⁻¹ := rfl
  have hF : F (n : ℂ) = 0 := by
    rw [h5, h3, h4, sub_self]
  have hlim : Filter.Tendsto F (𝓝 (n : ℂ)) (𝓝 (F (n : ℂ))) := by
    rw [hF]
    exact tendsto_pi_cot_sub n
  exact hlim

/-- If `sin (πz) = 0`, then `z` is an integer. -/
theorem int_of_sin_pi_mul_eq_zero {z : ℂ} (hz : Complex.sin (Real.pi * z) = 0) :
    z ∈ Set.range ((↑) : ℤ → ℂ) := by
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hz
  have h1 : Real.pi * z = (k : ℂ) * Real.pi := by
    rw [← hk, mul_comm]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have h2 : z = (k : ℂ) := by
    rw [← mul_left_inj' hpi, mul_comm, h1, mul_comm]
  exact ⟨k, h2.symm⟩

/-- `sin (πz)` is nonzero away from the integers. -/
theorem sin_pi_mul_ne_zero_of_not_mem {z : ℂ} (hz : z ∈ ℂ_ℤ) :
    Complex.sin (Real.pi * z) ≠ 0 := by
  intro h
  exact hz (int_of_sin_pi_mul_eq_zero h)

/-- `π · cot (π·)` is differentiable away from the integers. -/
theorem differentiableAt_cot_pi (z : ℂ) (hz : z ∈ ℂ_ℤ) :
    DifferentiableAt ℂ (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w)) z := by
  have hs : Complex.sin (Real.pi * z) ≠ 0 := sin_pi_mul_ne_zero_of_not_mem hz
  have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.cos w / Complex.sin w) (Real.pi * z) :=
    differentiableAt_cos.div differentiableAt_sin hs
  have h3 : (fun w : ℂ => Complex.cos w / Complex.sin w) = Complex.cot := by
    funext w
    rw [Complex.cot_eq_cos_div_sin]
  have h4 : DifferentiableAt ℂ Complex.cot (Real.pi * z) := h3 ▸ h2
  have hid : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id (𝕜 := ℂ) (x := z)
  have h5 : DifferentiableAt ℂ (fun w : ℂ => Real.pi * w) z := hid.const_mul Real.pi
  have h6 : DifferentiableAt ℂ (Complex.cot ∘ (fun w : ℂ => Real.pi * w)) z :=
    h4.comp _ h5
  have h7 : DifferentiableAt ℂ (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w)) z :=
    (differentiableAt_const (_ : ℂ)).mul h6
  simpa [Function.comp] using h7

end Uniq2

section Uniq3

open scoped Topology

/-- `cot` is an odd function, with the `1 / 0 = 0` convention. -/
theorem cot_neg (z : ℂ) : Complex.cot (-z) = -Complex.cot z := by
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, Complex.cos_neg, Complex.sin_neg,
    div_neg]

/-- The difference of the two functions of lecture 16: `h = g - g₀` with
`g₀ z = π · cot (πz)`, used in the uniqueness argument of lecture 16 p.7. -/
def cotDiff (z : ℂ) : ℂ := cotSeries z - Real.pi * Complex.cot (Real.pi * z)

/-- The definitional unfolding of `cotDiff`. -/
theorem cotDiff_apply (z : ℂ) :
    cotDiff z = cotSeries z - Real.pi * Complex.cot (Real.pi * z) := rfl

/-- `(a - c) - (b - c) = a - b`. -/
theorem sub_sub_sub_cancel (a b c : ℂ) : (a - c) - (b - c) = a - b := by ring

/-- The function `z ↦ g z - (z - n)⁻¹` is continuous at the integer `n`: by (b) of lecture 16 it
equals `cotRest n z + n⁻¹`, which is holomorphic near `n`. -/
theorem continuousAt_cotSeries_sub (n : ℤ) :
    ContinuousAt (fun z : ℂ => cotSeries z - (z - n)⁻¹) (n : ℂ) := by
  have h1 : (fun z : ℂ => cotSeries z - (z - n)⁻¹) = fun z : ℂ => cotRest n z + (n : ℂ)⁻¹ := by
    funext z
    rw [cotRest_eq_sub]
    dsimp only [cotTerm]
    ring
  rw [h1]
  exact (continuousAt_cotRest n).add continuousAt_const

/-- The difference `cotDiff` is continuous at every integer: the two poles at `n` cancel
(lecture 16 p.7). -/
theorem continuousAt_cotDiff (n : ℤ) : ContinuousAt cotDiff (n : ℂ) := by
  have h1 : ContinuousAt (fun z : ℂ => cotSeries z - (z - n)⁻¹) (n : ℂ) :=
    continuousAt_cotSeries_sub n
  have h2 : ContinuousAt (fun z : ℂ => Real.pi * Complex.cot (Real.pi * z) - (z - n)⁻¹) (n : ℂ) :=
    continuousAt_pi_cot_sub n
  have h3 : ContinuousAt (fun z : ℂ =>
      (cotSeries z - (z - n)⁻¹) - (Real.pi * Complex.cot (Real.pi * z) - (z - n)⁻¹)) (n : ℂ) :=
    h1.sub h2
  have h4 : (fun z : ℂ => (cotSeries z - (z - (n : ℂ))⁻¹) -
      (Real.pi * Complex.cot (Real.pi * z) - (z - (n : ℂ))⁻¹)) =ᶠ[𝓝 (n : ℂ)]
      fun z : ℂ => cotDiff z :=
    Filter.Eventually.of_forall fun z : ℂ =>
      sub_sub_sub_cancel (cotSeries z) (Real.pi * Complex.cot (Real.pi * z)) ((z - n)⁻¹)
  exact h3.congr h4

/-- `cotDiff` is differentiable away from the integers, by (a) of lecture 16. -/
theorem differentiableAt_cotDiff_of_mem (z : ℂ) (hz : z ∈ ℂ_ℤ) :
    DifferentiableAt ℂ cotDiff z := by
  have h1 : DifferentiableAt ℂ cotSeries z :=
    differentiableOn_cotSeries.differentiableAt (isOpen_integerComplement.mem_nhds hz)
  have h2 : DifferentiableAt ℂ (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w)) z :=
    differentiableAt_cot_pi z hz
  have h3 : DifferentiableAt ℂ (fun w : ℂ => cotSeries w - Real.pi * Complex.cot (Real.pi * w)) z :=
    h1.sub h2
  have h4 : (fun w : ℂ => cotDiff w) =ᶠ[𝓝 z]
      fun w : ℂ => cotSeries w - Real.pi * Complex.cot (Real.pi * w) :=
    Filter.Eventually.of_forall fun w : ℂ => cotDiff_apply w
  exact h3.congr_of_eventuallyEq h4

/-- `cotDiff` is differentiable at the integer `n`: the removable singularity theorem, using that
every other integer is at distance at least `1` from `n`. -/
theorem differentiableAt_cotDiff (n : ℤ) : DifferentiableAt ℂ cotDiff (n : ℂ) := by
  have hd : ∀ᶠ z in 𝓝[≠] (n : ℂ), DifferentiableAt ℂ cotDiff z := by
    rw [eventually_nhdsWithin_iff]
    refine eventually_of_mem (Metric.ball_mem_nhds (n : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
      fun z hz hne => ?_
    have hne' : z ≠ (n : ℂ) := by simpa using hne
    refine differentiableAt_cotDiff_of_mem z (mem_integerComplement_iff.mpr ?_)
    rintro ⟨m, hm⟩
    have hball : z ∈ Metric.closedBall (n : ℂ) (1 / 2) := Metric.ball_subset_closedBall hz
    have hz' : z = (m : ℂ) := hm.symm
    rcases eq_or_ne m n with hmn | hmn
    · exact hne' (by rw [hz', hmn])
    · exact ne_of_mem_closedBall_half hmn hball hz'
  have hc : ContinuousAt cotDiff (n : ℂ) := continuousAt_cotDiff n
  have hana := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hc
  exact hana.differentiableAt

/-- **The function `cotDiff` is entire** (lecture 16 p.7): the two poles cancel at every integer,
so the only possible singularities of `g - π · cot (π ·)` are removable. -/
theorem differentiable_cotDiff : Differentiable ℂ cotDiff := by
  intro z
  by_cases hz : z ∈ ℂ_ℤ
  · exact differentiableAt_cotDiff_of_mem z hz
  · have h2 : ∃ n : ℤ, (n : ℂ) = z := by
      apply Classical.byContradiction
      intro h
      exact hz (mem_integerComplement_iff.mpr h)
    obtain ⟨n, hn⟩ := h2
    rw [← hn]
    exact differentiableAt_cotDiff n

/-- `cotDiff` satisfies the duplication formula `(d)` of lecture 16 p.7, because both `g` and
`π · cot (π ·)` do. -/
theorem cotDiff_dup (z : ℂ) : cotDiff z + cotDiff (z + 1 / 2) = 2 * cotDiff (2 * z) := by
  have h1 : cotDiff z + cotDiff (z + 1 / 2) =
      (cotSeries z + cotSeries (z + 1 / 2)) -
        (Real.pi * Complex.cot (Real.pi * z) +
          Real.pi * Complex.cot (Real.pi * (z + 1 / 2))) := by
    rw [cotDiff_apply z, cotDiff_apply (z + 1 / 2)]
    ring
  have h2 : (2 : ℂ) * cotDiff (2 * z) = 2 * cotSeries (2 * z) -
      (2 : ℂ) * (Real.pi * Complex.cot (Real.pi * (2 * z))) := by
    rw [cotDiff_apply (2 * z)]
    ring
  rw [h1, h2, cotSeries_dup z, cot_pi_dup z]

/-- `cotDiff` is an odd function, by (c) of lecture 16. -/
theorem cotDiff_neg (z : ℂ) : cotDiff (-z) = -cotDiff z := by
  have h1 : Real.pi * (-z) = -(Real.pi * z) := by ring
  have h2 : Real.pi * Complex.cot (-(Real.pi * z)) = -(Real.pi * Complex.cot (Real.pi * z)) := by
    rw [cot_neg, mul_neg]
  rw [cotDiff_apply (-z), cotDiff_apply z, cotSeries_neg, h1, h2]
  ring

/-- A complex number that equals its own negation is `0`. -/
theorem eq_zero_of_eq_neg (a : ℂ) (h : a = -a) : a = 0 := by
  have h2 : a + a = 0 :=
    (congrArg (fun x : ℂ => x + a) h).trans (neg_add_cancel a)
  have h3 : (2 : ℂ) * a = 0 := by
    rw [two_mul]
    exact h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (by norm_num : (2 : ℂ) ≠ 0)
  · exact h4

/-- **(The partial fraction expansion of `π · cot (π ·)`, Conway VIII.5.3, lecture 16 p.7)** The
function `g = Conway.cotSeries` of lecture 16, which satisfies (a)-(d), is `π · cot (π ·)`: the
difference of the two is entire by the removable singularity theorem, constant by Herglotz' lemma,
and zero because it is odd. -/
theorem cotSeries_eq_cot_pi (z : ℂ) : cotSeries z = Real.pi * Complex.cot (Real.pi * z) := by
  obtain ⟨c, hc⟩ := exists_eq_const_of_cot_dup cotDiff differentiable_cotDiff
    (fun z => (cotDiff_dup z).symm)
  have h0 : cotDiff 0 = 0 := eq_zero_of_eq_neg (cotDiff 0) (by simpa using cotDiff_neg 0)
  have h1 : c = 0 := by
    rw [← hc 0]
    exact h0
  have h2 : cotDiff z = 0 := by
    rw [hc z, h1]
  rw [← sub_eq_zero, ← cotDiff_apply z]
  exact h2

end Uniq3

/-- A point of `ℂ − ℤ` differs from every integer. -/
theorem ne_of_mem_integerComplement {z : ℂ} (hz : z ∈ ℂ_ℤ) (n : ℤ) : z ≠ n := by
  intro h
  exact hz ⟨n, h.symm⟩

/-- The derivative of one summand of `g`: `d/dz (1/(z-n) + 1/n) = -1/(z-n)²`. -/
theorem deriv_cotTerm (n : ℤ) (z : ℂ) (hz : z ≠ n) :
    deriv (fun w : ℂ => cotTerm n w) z = -((z - n)⁻¹ ^ 2) := by
  have hne : (z : ℂ) - n ≠ 0 := sub_ne_zero.mpr hz
  have h1 : HasDerivAt (fun w : ℂ => w - n) (1 : ℂ) z := by
    have h : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id (𝕜 := ℂ) (x := z)
    convert h.sub (hasDerivAt_const z (n : ℂ)) using 1
    · simp
  have h2 : HasDerivAt (fun w : ℂ => (1 : ℂ) / (w - n))
      (((0 : ℂ) * (z - n) - (1 : ℂ) * 1) / (z - n) ^ 2) z :=
    (hasDerivAt_const z (1 : ℂ)).div h1 hne
  have hval : ((0 : ℂ) * (z - n) - (1 : ℂ) * 1) / (z - n) ^ 2 = -((z - n)⁻¹ ^ 2) := by
    rw [div_eq_mul_inv, inv_pow]
    ring
  rw [hval] at h2
  have h3 : HasDerivAt (fun w : ℂ => cotTerm n w) (-((z - n)⁻¹ ^ 2)) z := by
    have h := h2.add (hasDerivAt_const z ((n : ℂ)⁻¹))
    rw [add_zero] at h
    exact h
  rw [h3.deriv]

/-- `Complex.cot` has derivative `-1 / sin²` away from the zeros of `sin`. -/
theorem hasDerivAt_cot (x : ℂ) (hs : Complex.sin x ≠ 0) :
    HasDerivAt Complex.cot (-((Complex.sin x)⁻¹ ^ 2)) x := by
  have hA : HasDerivAt (fun w : ℂ => Complex.cos w / Complex.sin w)
      ((-Complex.sin x * Complex.sin x - Complex.cos x * Complex.cos x) / Complex.sin x ^ 2) x :=
    (hasDerivAt_cos x).div (hasDerivAt_sin x) hs
  have hB : (-Complex.sin x * Complex.sin x - Complex.cos x * Complex.cos x) /
      Complex.sin x ^ 2 = -((Complex.sin x)⁻¹ ^ 2) := by
    have h1 : -Complex.sin x * Complex.sin x - Complex.cos x * Complex.cos x = -1 := by
      rw [show -Complex.sin x * Complex.sin x - Complex.cos x * Complex.cos x =
          -((Complex.sin x) ^ 2 + (Complex.cos x) ^ 2) by ring, sin_sq_add_cos_sq]
    rw [h1, div_eq_mul_inv, inv_pow]
    ring
  rw [hB] at hA
  convert hA using 1
  · funext w
    rw [Complex.cot_eq_cos_div_sin]

/-- The derivative of `w ↦ π · w` is `π`. -/
theorem hasDerivAt_pi_mul (z : ℂ) : HasDerivAt (fun w : ℂ => Real.pi * w) (Real.pi : ℂ) z := by
  have h : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id (𝕜 := ℂ) (x := z)
  have h2 := h.const_mul (Real.pi : ℂ)
  rw [mul_one] at h2
  exact h2

/-- The derivative of `π · cot (π ·)` away from the integers. -/
theorem deriv_pi_cot_pi (z : ℂ) (hz : z ∈ ℂ_ℤ) :
    deriv (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w)) z =
      -((Real.pi : ℂ) ^ 2 * (Complex.sin (Real.pi * z))⁻¹ ^ 2) := by
  have hs : Complex.sin (Real.pi * z) ≠ 0 := sin_pi_mul_ne_zero_of_not_mem hz
  have hpi := hasDerivAt_pi_mul z
  have hcomp := (hasDerivAt_cot (Real.pi * z) hs).comp z hpi
  have houter : HasDerivAt (fun w : ℂ => Real.pi * Complex.cot (Real.pi * w))
      ((Real.pi : ℂ) * (-((Complex.sin (Real.pi * z))⁻¹ ^ 2) * (Real.pi : ℂ))) z :=
    hcomp.const_mul (Real.pi : ℂ)
  rw [houter.deriv]
  ring

/-- The M-test estimate for the differentiated series: `1 / (z - n)²` is `O(1/n²)` on a disc. -/
theorem deriv_cotTerm_bound (r : ℝ) (n : ℤ) (z : ℂ) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hn : (2 * r + 1 : ℝ) < ‖(n : ℂ)‖) :
    ‖((z : ℂ) - n)⁻¹ ^ 2‖ ≤ (4 : ℝ) * (‖(n : ℂ)‖⁻¹ ^ 2) := by
  have hne : (z : ℂ) ≠ n := by
    intro h
    have h1 : ‖(n : ℂ)‖ ≤ r := by
      rw [← h]
      exact hz
    linarith
  have hu : (0 : ℝ) < ‖(n : ℂ)‖ := by
    have h1 : (0 : ℝ) ≤ r := hr
    linarith [norm_nonneg (n : ℂ)]
  have hv : (0 : ℝ) < ‖(z : ℂ) - n‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have h2 : ‖(n : ℂ)‖ - r ≤ ‖(z : ℂ) - n‖ := by
    have h3 := norm_sub_norm_le (n : ℂ) z
    rw [norm_sub_rev] at h3
    linarith [hz]
  have hur : (0 : ℝ) < ‖(n : ℂ)‖ - r := by linarith
  have h3 : ‖(z : ℂ) - n‖⁻¹ ≤ (‖(n : ℂ)‖ - r)⁻¹ := (inv_le_inv₀ hv hur).mpr h2
  have hE : (‖(n : ℂ)‖ - r)⁻¹ ≤ 2 * ‖(n : ℂ)‖⁻¹ := by
    have h5 : (2 : ℝ) * ‖(n : ℂ)‖⁻¹ = (‖(n : ℂ)‖ / 2)⁻¹ := by field_simp
    rw [h5]
    refine (inv_le_inv₀ hur (by linarith)).mpr ?_
    linarith
  calc ‖((z : ℂ) - n)⁻¹ ^ 2‖ = ‖(z : ℂ) - n‖⁻¹ ^ 2 := by rw [norm_pow, norm_inv]
    _ ≤ (‖(n : ℂ)‖ - r)⁻¹ ^ 2 := by gcongr
    _ ≤ (2 * ‖(n : ℂ)‖⁻¹) ^ 2 := by gcongr
    _ = (4 : ℝ) * (‖(n : ℂ)‖⁻¹ ^ 2) := by ring

/-- The summable majorant `4 / n²` of the differentiated series. -/
theorem summable_deriv_cotMajorant : Summable fun n : ℤ => (4 : ℝ) * (‖(n : ℂ)‖⁻¹ ^ 2) :=
  Summable.mul_left (4 : ℝ)
    (Summable.congr
      ((Real.summable_one_div_int_pow (p := 2)).2 (by norm_num : (1 : ℕ) < 2)) fun n => by simp)

/-- The differentiated series `Σ -1 / (z - n)²` converges normally on `ℂ − ℤ`. -/
theorem summableLocallyUniformlyOn_deriv_cotTerm :
    SummableLocallyUniformlyOn (fun n : ℤ => (fun z : ℂ => -((z - n)⁻¹ ^ 2))) ℂ_ℤ := by
  refine SummableLocallyUniformlyOn.of_locally_bounded_eventually isOpen_integerComplement ?_
  intro K hK hKc
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mp hKc.isBounded
  set r : ℝ := max R 0 with hrdef
  refine ⟨fun n => (4 : ℝ) * (‖(n : ℂ)‖⁻¹ ^ 2), summable_deriv_cotMajorant, ?_⟩
  filter_upwards
      [Finset.eventually_cofinite_notMem (Finset.Icc (-(⌈2 * r + 1⌉₊ : ℤ)) ⌈2 * r + 1⌉₊)] with n hn
  intro z hz
  have hz' : ‖(z : ℂ)‖ ≤ r := by
    have h1 : dist z 0 ≤ r := (hR hz).trans (le_max_left R 0)
    simpa [hrdef] using h1
  have hr : 0 ≤ r := le_max_right R 0
  simp only [norm_neg]
  exact deriv_cotTerm_bound r n z hr hz' (cot_cofinite_bound r hn)

/-- `derivWithin` on `ℂ − ℤ` of one summand of `g`. -/
theorem derivWithin_cotTerm (n : ℤ) (z : ℂ) (hz : z ∈ ℂ_ℤ) :
    derivWithin (fun w : ℂ => cotTerm n w) ℂ_ℤ z = -((z - n)⁻¹ ^ 2) := by
  rw [derivWithin_of_isOpen isOpen_integerComplement hz]
  exact deriv_cotTerm n z (ne_of_mem_integerComplement hz n)

/-- **Term by term differentiation of `g`** (lecture 16 p.5): for `z ∈ ℂ − ℤ`,
`deriv g z = Σ_{n ∈ ℤ} -1 / (z - n)²`. -/
theorem deriv_cotSeries (z : ℂ) (hz : z ∈ ℂ_ℤ) :
    deriv cotSeries z = ∑' n : ℤ, -((z - n)⁻¹ ^ 2) := by
  have h1 : SummableLocallyUniformlyOn (fun n : ℤ =>
      (fun w : ℂ => derivWithin (fun v : ℂ => cotTerm n v) ℂ_ℤ w)) ℂ_ℤ :=
    SummableLocallyUniformlyOn_congr (fun n w hw => (derivWithin_cotTerm n w hw).symm)
      summableLocallyUniformlyOn_deriv_cotTerm
  have h2 := derivWithin_tsum isOpen_integerComplement hz (fun y _ => summable_cotTerm y) h1
    (fun n r hr => differentiableAt_cotTerm (ne_of_mem_integerComplement hr n))
  have h3 : (∑' n : ℤ, derivWithin (cotTerm n) ℂ_ℤ z) = ∑' n : ℤ, -((z - n)⁻¹ ^ 2) :=
    tsum_congr fun n => by
      rw [derivWithin_of_isOpen isOpen_integerComplement hz,
        deriv_cotTerm n z (ne_of_mem_integerComplement hz n)]
  rw [derivWithin_of_isOpen isOpen_integerComplement hz] at h2
  rw [h3] at h2
  exact h2

/-- **Corollary** (lecture 16 p.5): differentiating the partial fraction expansion of
`π · cot (π ·)` term by term gives `π² / sin (π z)² = Σ_{n ∈ ℤ} 1 / (z - n)²` on `ℂ − ℤ`.

*Deviation from the notes.* The lecture writes the summand as `1 / (z² - n²)`, which is a
slip: the term by term derivative of `1 / (z - n) + n⁻¹` is `-1 / (z - n)²`, as here, and
the notes' right hand side instead sums to `π · cot (π z) / z`, which vanishes at
`z = 1 / 2`. -/
theorem pi_sq_div_sin_sq (z : ℂ) (hz : z ∈ ℂ_ℤ) :
    (Real.pi : ℂ) ^ 2 * (Complex.sin (Real.pi * z))⁻¹ ^ 2 = ∑' n : ℤ, ((z - n)⁻¹) ^ 2 := by
  have h1 : deriv cotSeries z = -((Real.pi : ℂ) ^ 2 * (Complex.sin (Real.pi * z))⁻¹ ^ 2) := by
    have h : cotSeries = fun w : ℂ => Real.pi * Complex.cot (Real.pi * w) :=
      funext fun w => cotSeries_eq_cot_pi w
    rw [h, deriv_pi_cot_pi z hz]
  have h2 : deriv cotSeries z = -∑' n : ℤ, ((z - n)⁻¹) ^ 2 := by
    rw [deriv_cotSeries z hz, tsum_neg]
  exact (neg_inj.mp (h2.symm.trans h1)).symm

end Conway

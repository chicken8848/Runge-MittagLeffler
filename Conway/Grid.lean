/-
Copyright (c) 2026 MA5217 formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MA5217 formalization project (Conway, Chapter VIII)
-/
module

public import Conway.Cauchy
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Topology.Order.Compact

/-!
# MA5217 / Conway Chapter VIII, §1: the grid of squares and the Separation Lemma

This file contains the proof of the **Enhanced Separation Lemma**
(`Conway.enhancedSeparationLemma` in `Conway/Separation.lean`), i.e. the topological input of the
lecturer's proof of Runge's theorem (lecture 13 p.2; Conway VIII.1.1 Proposition, p.195–196).

Conway's proof, which is the proof given here:

* "Observe that by enlarging `K` a little we may assume that `K = cl(int K)`.  Let
  `0 < σ < (√2)⁻¹ d(K, ℂ − G)` and place a grid of horizontal and vertical lines in the plane such
  that consecutive lines are less than a distance `σ` apart" — `Conway.exists_neighbourhood_subset`
  and `Conway.square`;
* "Let `R₁, …, Rₘ` be the resulting rectangles that intersect `K` (there are only a finite number of
  them because `K` is compact).  Also let `∂Rⱼ` be the boundary of `Rⱼ` … considered as a polygon
  with the counter-clockwise direction" — `Conway.cells`, `Conway.cells_finite` and
  `Conway.integralSegSquare`;
* "… many of the sides of the rectangles `R₁, …, Rₘ` will intersect.  Suppose `Rⱼ` and `Rₗ` have a
  common side … from the direction given `∂Rⱼ` and `∂Rₗ`, `uⱼ` and `uₗ` are directed in the opposite
  sense, so if `g` is any continuous function … `∫ g + ∫ g = 0`.  Let `γ₁, …, γₙ` be those directed
  line segments that constitute a side of exactly one of the `Rⱼ`.  Thus
  `Σⱼ ∫_{∂Rⱼ} g = Σₖ ∫_{γₖ} g` (1.2)" — `Conway.integralSegSquare_sum`, proved the way the lecture's
  "the inner sides cancel" is: `Conway.integralSegGrid_insert` (adding one square), whose two cases
  are `Conway.integralSegGrid_shared` (a side shared with a square that is not in the family
  contributes `0` by Cauchy–Goursat on the rectangle it bounds) and
  `Conway.integralSegGrid_new` (the new square contributes its own four sides);
* "We claim that each `γₖ` is in `G − K`.  In fact, if one of the `γₖ` intersects `K`, it is easy to
  see that there are two rectangles in the grid with `γₖ` as a side and so both meet `K`" —
  `Conway.supportGrid_subset_diff`;
* "If `z` belongs to `K` and is not on the boundary of any `Rⱼ` then … `z` belongs to the interior of
  exactly one `Rⱼ`; if `z ∉ Rⱼ` this integral equals `0`, and if `z` is in `Rⱼ` this integral equals
  `f(z)` by Cauchy's Formula … But both sides of (1.4) are continuous functions on `K` (because each
  `γₖ` misses `K`) and they agree on a dense subset of `K`" — `Conway.sum_integralSegGrid_eq`,
  `Conway.continuousOn_sum_integralSegGrid`, `Conway.exists_mem_cells_of_mem`;
* the last step of the lemma of lecture 13 ("write `E = E₁ + ⋯ + Eₙ` where each `Eⱼ` is of length
  `< δ`", which leaves the traced set, and hence its distance to `K`, unchanged):
  `Conway.segIntegral_subdiv`.
-/

@[expose] public section

open scoped BigOperators Convex
open Set Filter intervalIntegral MeasureTheory AffineMap

namespace Conway

noncomputable section

variable {K G : Set ℂ}

/-! ## Enlarging `K` a little -/

/-- `‖v‖ ≤ |v.re| + |v.im|`. -/
theorem norm_le_abs_re_add_abs_im (v : ℂ) : ‖v‖ ≤ |v.re| + |v.im| := by
  have hv : v = (v.re : ℂ) + (v.im : ℂ) * Complex.I := Complex.re_add_im v
  have h1 : ‖(v.re : ℂ) + (v.im : ℂ) * Complex.I‖ ≤ ‖(v.re : ℂ)‖ + ‖(v.im : ℂ) * Complex.I‖ :=
    norm_add_le _ _
  have h2 : ‖(v.im : ℂ) * Complex.I‖ = |v.im| := by
    rw [norm_mul, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have h3 : ‖(v.re : ℂ)‖ = |v.re| := Real.norm_eq_abs
  rw [hv, h3, h2] at h1
  exact h1

/-- **Enlarging `K` a little** (Conway VIII.1.1 "by enlarging `K` a little …", lecture 13 p.2 "choose
`0 < σ < (√2)⁻¹ d(K, ℂ − G)`"): if `K ⊆ G` with `K` compact and `G` open, then some `ρ > 0` has the
property that the open `5ρ`-neighbourhood of `K` still lies in `G`.  The large factor `5` leaves
room for the grid squares of radius `≤ 2ρ` constructed below. -/
theorem exists_neighbourhood_subset (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G) :
    ∃ ρ : ℝ, 0 < ρ ∧ {z | ∃ w ∈ K, ‖z - w‖ < 5 * ρ} ⊆ G := by
  rcases eq_empty_or_nonempty K with hK0 | hK1
  · exact ⟨1, by positivity, by simpa using hK0⟩
  · -- one admissible radius at each point of `K`, halved, and a finite subcover
    obtain ⟨p₀, hp₀⟩ := hK1
    let ι : Type := { x : ℂ × ℝ // x.1 ∈ K ∧ 0 < x.2 ∧ Metric.ball x.1 x.2 ⊆ G }
    let U : ι → Set ℂ := fun x => Metric.ball x.1.1 (x.1.2 / 2)
    have hU : K ⊆ ⋃ x : ι, U x := by
      intro z hz
      obtain ⟨r, hr0, hr⟩ := Metric.isOpen_iff.mp hG z hz
      refine mem_iUnion.mpr ⟨⟨(z, r), ⟨hz, hr0, hr⟩⟩, ?_⟩
      simpa [U] using Metric.mem_ball_self (by linarith : (0 : ℝ) < r / 2)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover U (fun _ => isOpen_ball) hU
    have ht0 : t.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.coe_empty, biUnion_empty] at ht
      exact absurd (ht hp₀) (Set.not_mem_empty _)
    obtain ⟨rho, hrho0, hrho⟩ := by
      classical
      have hne : (t.image (fun x : ι => x.1.2 / 16)).Nonempty := Finset.nonempty_image_iff.mpr ht0
      refine ⟨_, Finset.lt_min'.mpr (fun y hy => ?_), fun x hx => ?_⟩
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        linarith [x.2.2.1]
      · exact Finset.min'_le _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    refine ⟨rho, hrho0, fun z hz => ?_⟩
    obtain ⟨w, hw, hzw⟩ := hz
    obtain ⟨x, hx, hwx⟩ := Finset.mem_biUnion.mp (ht hw)
    rw [U, Metric.mem_ball] at hwx
    rw [Metric.mem_ball] at hzw
    have htri : dist z x.1.1 ≤ dist z w + dist w x.1.1 := dist_triangle _ _ _
    exact x.2.2.2 (by rw [Metric.mem_ball]; linarith [x.2.2.1, hrho x hx])

/-! ## Contour integrals along a segment, in the two conventions -/

/-- The contour integral of a density `φ` along the segment `[a,b]`:

    `segContour φ a b = ∫₀¹ φ (lineMap a b t) * (b - a) dt`,

i.e. Mathlib's `curveIntegral` of the `1`-form `φ(w) dw` over the path `lineMap a b` (the
parametrisation is the same by Mathlib's `curveIntegral_segment`).  `Conway.segIntegral` is the
special case of the Cauchy density `φ(w) * (w - z)⁻¹`: `Conway.segIntegral_eq_segContour`. -/
noncomputable def segContour (φ : ℂ → ℂ) (a b : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, φ (lineMap a b t) * (b - a)

/-- The Cauchy transform of a segment is the contour integral of the Cauchy density. -/
theorem segIntegral_eq_segContour (φ : ℂ → ℂ) (a b z : ℂ) :
    segIntegral φ a b z = segContour (fun w ↦ φ w * (w - z)⁻¹) a b := rfl

/-- `∫ x in a..b, F x = (b - a) • ∫ t in (0)..1, F (a + (b - a) * t)`: the affine change of
variable `t ↦ a + (b - a) * t`, in the form used by `Conway.segContour`. -/
theorem integral_affine (F : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, F x = (b - a) • ∫ t in (0 : ℝ)..1, F (a + (b - a) * t) := by
  have h1 : a + (b - a) * (0 : ℝ) = a := by abel
  have h2 : a + (b - a) * (1 : ℝ) = b := by abel
  rw [← h1, ← h2, intervalIntegral.smul_integral_comp_add_mul]

/-- Pull the constant `(b - a)` out of the parametrized integral, in the exact form needed to
compare `Conway.segContour` with `Conway.integral_affine`. -/
theorem segContour_eq_smul (φ : ℂ → ℂ) (a b : ℂ) :
    segContour φ a b = (b - a) • ∫ t in (0 : ℝ)..1, φ (lineMap a b t) := by
  have h : ∀ t : ℝ, φ (lineMap a b t) * (b - a) = (b - a) • φ (lineMap a b t) := by
    intro t
    rw [Complex.smul_def, mul_comm]
  show ∫ t in (0 : ℝ)..1, φ (lineMap a b t) * (b - a) = _
  rw [h]
  rw [integral_smul]

/-- The parametrisation of the horizontal segment `p + c*I` to `q + c*I` in the coordinates of
`Conway.integral_affine`. -/
theorem lineMap_side_real (p q c : ℝ) (t : ℝ) :
    lineMap (↑p + ↑c * Complex.I) (↑q + ↑c * Complex.I) t = ↑(p + (q - p) * t) + ↑c * Complex.I := by
  rw [lineMap_apply', sub_smul, add_smul, add_smul, one_smul]
  refine Complex.ext ?_ ?_ <;> simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_zero, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_add, sub_self, Complex.ofReal_re, Complex.ofReal_im] <;> ring

/-- The parametrisation of the vertical segment `r + c*I` to `r + d*I`. -/
theorem lineMap_side_imag (r c d : ℝ) (t : ℝ) :
    lineMap (↑r + ↑c * Complex.I) (↑r + ↑d * Complex.I) t = ↑r + ↑(c + (d - c) * t) * Complex.I := by
  rw [lineMap_apply', sub_smul, add_smul, add_smul, one_smul]
  refine Complex.ext ?_ ?_ <;> simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_zero, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_add, sub_self, Complex.ofReal_re, Complex.ofReal_im] <;> ring

/-- **The horizontal side, translated between the two conventions**: `∫ x in p..q, φ (x + c*I)`,
the form in which Mathlib's `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
writes the lower side of a rectangle, is the contour integral of `φ` along the segment. -/
theorem segContour_side_real (φ : ℂ → ℂ) (p q c : ℝ) :
    segContour φ (↑p + ↑c * Complex.I) (↑q + ↑c * Complex.I) = ∫ x in p..q, φ (↑x + ↑c * Complex.I) := by
  rw [segContour_eq_smul, integral_affine]
  congr 1 with t
  rw [lineMap_side_real]

/-- **The vertical side, translated between the two conventions**: Mathlib writes the right side of
a rectangle as `Complex.I • ∫ y in c..d, φ (r + y*I)`. -/
theorem segContour_side_imag (φ : ℂ → ℂ) (r c d : ℝ) :
    segContour φ (↑r + ↑c * Complex.I) (↑r + ↑d * Complex.I) =
      Complex.I • ∫ y in c..d, φ (↑r + ↑y * Complex.I) := by
  rw [segContour_eq_smul, integral_affine]
  rw [← smul_smul]
  congr 1 with t
  rw [lineMap_side_imag]

/-- The counter-clockwise boundary integral `∮_{∂R}` of the density `φ` over the rectangle with two
opposite corners `p`, `q`: the sum of the four sides `segContour`.  This is Conway's `∂Rⱼ`
"considered as a polygon with the counter-clockwise direction". -/
def integralSegRect (φ : ℂ → ℂ) (p q : ℂ) : ℂ :=
  segContour φ (↑p.re + ↑p.im * Complex.I) (↑q.re + ↑p.im * Complex.I) +
    segContour φ (↑q.re + ↑p.im * Complex.I) (↑q.re + ↑q.im * Complex.I) +
      segContour φ (↑q.re + ↑q.im * Complex.I) (↑p.re + ↑q.im * Complex.I) +
        segContour φ (↑p.re + ↑q.im * Complex.I) (↑p.re + ↑p.im * Complex.I)

/-- **Cauchy's theorem on a rectangle** in the `segContour` convention: if the density `φ` is
continuous on the closed rectangle and differentiable off the countable set `s`, its integral over
the counter-clockwise boundary vanishes. -/
theorem integral_boundary_rect_eq_zero_of_differentiable_on_off_countor
    (φ : ℂ → ℂ) (p q : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn φ ([[p.re, q.re]] ×ℂ [[p.im, q.im]]))
    (Hd : ∀ x ∈ Ioo (min p.re q.re) (max p.re q.re) ×ℂ Ioo (min p.im q.im) (max p.im q.im) \ s,
      DifferentiableAt ℂ φ x) :
    integralSegRect φ p q = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable φ p q s hs Hc
    Hd
  rw [← segContour_side_real, ← segContour_side_imag, ← segContour_side_real, ← segContour_side_imag,
    ← segContour_side_imag, ← segContour_side_real, ← segContour_side_real] at h
  rw [integralSegRect]
  have h1 : segContour φ (↑q.re + ↑q.im * Complex.I) (↑p.re + ↑q.im * Complex.I) =
      -segContour φ (↑p.re + ↑q.im * Complex.I) (↑q.re + ↑q.im * Complex.I) := segContour_reversal _ _ _
  have h2 : segContour φ (↑p.re + ↑q.im * Complex.I) (↑p.re + ↑p.im * Complex.I) =
      -segContour φ (↑p.re + ↑p.im * Complex.I) (↑p.re + ↑q.im * Complex.I) := segContour_reversal _ _ _
  rw [h1, h2]
  abel


/-- A closed square of the grid of Conway VIII.1.1: `square η i j` is the closed square whose centre
is the lattice point `(i : ℝ) * η.re + (j : ℝ) * η.im * Complex.I` and whose half side lengths are
`η.re / 2` and `η.im / 2`.  The grid lines are `η.re * ℤ + η.re / 2` horizontally and
`η.im * ℤ + η.im / 2` vertically, so consecutive lines are `|η.re|` and `|η.im|` apart. -/
def square (η : ℂ) (i j : ℤ) : Set ℂ :=
  { z | (i : ℝ) * η.re - η.re / 2 ≤ z.re ∧ z.re ≤ (i : ℝ) * η.re + η.re / 2 ∧
      (j : ℝ) * η.im - η.im / 2 ≤ z.im ∧ z.im ≤ (j : ℝ) * η.im + η.im / 2 }

/-- The indices of the squares that meet `K`: Conway's `R₁, …, Rₘ`. -/
def cells (η : ℂ) (K : Set ℂ) : Set (ℤ × ℤ) :=
  { p | (square η p.1 p.2) ∩ K ≠ ∅ }

/-- A set of integers that is bounded in `ℝ` is finite. -/
theorem Set.finite_setOf_int_abs_le (B : ℝ) : { i : ℤ | |(i : ℝ)| ≤ B }.Finite :=
  Set.Finite.subset Set.finite_Icc (by
    intro i hi
    rw [mem_Icc]
    exact ⟨Int.ceil_le.mpr (by linarith [abs_le.mp hi]), Int.le_floor.mpr (by
      have := abs_le.mp hi
      linarith [abs_le.mpr this])⟩)

/-- **Conway VIII.1.1: "there are only a finite number of them because `K` is compact"**. -/
theorem cells_finite (hK : IsCompact K) {η : ℂ} (hη : 0 < η.re ∧ 0 < η.im) :
    (cells η K).Finite := by
  rcases eq_empty_or_nonempty K with hK0 | hK1
  · have : cells η K = ∅ := by
      ext p
      simp [cells, hK0, Set.inter_empty, Set.nonempty_iff_ne_empty]
    rw [this]
    exact Set.finite_empty
  · obtain ⟨p, hp⟩ := hK1
    obtain ⟨x, hxK, hx⟩ := hK.exists_isMaxOn ⟨p, hp⟩ continuousOn_norm
    set R : ℝ := ‖x‖ + 1 with hRdef
    have hR : ∀ z ∈ K, ‖z‖ < R := fun z hz => by
      have := hx z hz
      linarith [norm_nonneg x]
    have hfin : { p : ℤ × ℤ | |(p.1 : ℝ)| ≤ R / η.re + 1 ∧ |(p.2 : ℝ)| ≤ R / η.im + 1 }.Finite := by
      have h1 : { i : ℤ | |(i : ℝ)| ≤ R / η.re + 1 }.Finite := Set.finite_setOf_int_abs_le _
      have h2 : { i : ℤ | |(i : ℝ)| ≤ R / η.im + 1 }.Finite := Set.finite_setOf_int_abs_le _
      refine Set.Finite.subset (h1.prod h2) ?_
      rintro ⟨i, j⟩ ⟨h1, h2⟩
      exact ⟨h1, h2⟩
    refine Set.Finite.subset hfin ?_
    rintro ⟨i, j⟩ hp
    obtain ⟨z, hz, hzK⟩ := Set.nonempty_of_ne_empty hp
    have hre : |(i : ℝ) * η.re - z.re| ≤ η.re / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have him : |(j : ℝ) * η.im - z.im| ≤ η.im / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hz.4], by linarith [hz.3]⟩
    have hR' : |z.re| < R ∧ |z.im| < R := by
      refine ⟨?_, ?_⟩
      · calc |z.re| = ‖(z.re : ℂ)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖z‖ := by
              have := norm_re_le_norm z
              rwa [Complex.norm_C] at this
          _ < R := hR z hzK
      · calc |z.im| = ‖(z.im : ℂ)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖z‖ := by
              have := norm_im_le_norm z
              rwa [Complex.norm_C] at this
          _ < R := hR z hzK
    refine ⟨?_, ?_⟩
    · rw [abs_le]
      refine ⟨by
        have h0 : 0 ≤ η.re := by linarith [hz.1, hz.2]
        have h1 : |(i : ℝ)| * η.re = |(i : ℝ) * η.re| := by rw [abs_mul, abs_of_nonneg h0]
        have h2 : |(i : ℝ) * η.re| ≤ |z.re| + η.re / 2 := by
          calc |(i : ℝ) * η.re| = |(i : ℝ) * η.re - z.re + z.re| := by congr 1; abel
            _ ≤ |(i : ℝ) * η.re - z.re| + |z.re| := abs_add _ _
            _ ≤ η.re / 2 + |z.re| := by linarith [hre]
        have h3 : (i : ℝ) ≥ -(|z.re| / η.re + 1 / 2) := by
          have h4 : (-(|z.re| + η.re / 2) : ℝ) ≤ (i : ℝ) * η.re := by
            linarith [abs_le.mp h1, h2]
          field_simp at h4 ⊢
          nlinarith [hz.1, hz.2]
        linarith, by
        have h0 : 0 ≤ η.re := by linarith [hz.1, hz.2]
        have h2 : |(i : ℝ) * η.re| ≤ |z.re| + η.re / 2 := by
          calc |(i : ℝ) * η.re| = |(i : ℝ) * η.re - z.re + z.re| := by congr 1; abel
            _ ≤ |(i : ℝ) * η.re - z.re| + |z.re| := abs_add _ _
            _ ≤ η.re / 2 + |z.re| := by linarith [hre]
        have h4 : (i : ℝ) * η.re ≤ |z.re| + η.re / 2 := (abs_le.mp h2).2
        field_simp at h4 ⊢
        nlinarith [hz.1, hz.2]⟩
    · rw [abs_le]
      have h0 : 0 ≤ η.im := by linarith [hz.3, hz.4]
      have h2 : |(j : ℝ) * η.im| ≤ |z.im| + η.im / 2 := by
        calc |(j : ℝ) * η.im| = |(j : ℝ) * η.im - z.im + z.im| := by congr 1; abel
          _ ≤ |(j : ℝ) * η.im - z.im| + |z.im| := abs_add _ _
          _ ≤ η.im / 2 + |z.im| := by linarith [him]
      refine ⟨by
        have h4 : (-(|z.im| + η.im / 2) : ℝ) ≤ (j : ℝ) * η.im := (abs_le.mp h2).1
        field_simp at h4 ⊢
        nlinarith [hz.3, hz.4], by
        have h4 : (j : ℝ) * η.im ≤ |z.im| + η.im / 2 := (abs_le.mp h2).2
        field_simp at h4 ⊢
        nlinarith [hz.3, hz.4]⟩

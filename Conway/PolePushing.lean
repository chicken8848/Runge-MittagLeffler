/-
Copyright (c) 2026 MA5217 formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MA5217 formalization project (Conway, Chapter VIII)
-/

module

public import Conway.Basic
public import Conway.Geom

/-!
# MA5217 / Conway Chapter VIII, §1: the pole pushing lemma

This file contains the *pole pushing* lemma (lecture 14 p.3–4), i.e. the induction step of the
lecturer's proof of Runge's theorem (Conway VIII.1.7): let `K ⊆ ℂ` be compact, `z₀ ∉ K`, and let
`b` be a point that lies closer to `K` than `z₀` does — more precisely `‖z₀ - b‖ + d ≤ ‖z - b‖` on
`K` for some `d > 0`, so that the closed ball `closedBall b (‖z₀ - b‖ + d / 2)` contains `K` but
misses the segment `[z₀, b]`.  Then the generator `z ↦ (z - z₀)⁻¹` is the uniform limit on `K` of
the partial sums `Conway.laureanSum` of its Laurent expansion in powers of `(z - b)⁻¹`, which have
their only pole at `b`: `Conway.approximable_PoleAt_of_polePush`.

The lecturer obtains the approximants in two equivalent ways, and we formalize the second one
(the first being available as `Conway.approximable_segIntegral_of_separation`):

* the Cauchy transform of the segment `[z₀, b]`, expanded in a geometric series;
* the "normally convergent" geometric series of lecture 13 p.4 / Conway VIII.1.6, whose error
  estimate is `Conway.norm_invSub_sub_laureanSum_le`.

Iterating ("pushing") the pole along a polygonal chain `z₀ = w₀, w₁, …` inside the component of
`Kᶜ` that contains `z₀`, with each segment shorter than the positive distance from `K` to the
chain, moves the pole to any prescribed point of that component.  If the component is unbounded,
the pole can be pushed outside a large disc, where the Taylor expansion
(`Conway.approximable_Polys_of_ball`, with the partial sums `Conway.taylorSum`) replaces the pole by
`∞`; this is the lecturer's "if `w = ∞`, choose `a` and `R` with `K ⊆ B(a;R)` and `z₀ ∉ B(a;R)`".
-/

@[expose] public section

open Set Filter TopologicalSpace Metric
open scoped BigOperators

namespace Conway

noncomputable section

variable {K : Set ℂ}

/-- `PolePush K b z₀`: the pole of the generator `z ↦ (z - z₀)⁻¹` may be pushed to `b`: `b` is
closer to every point of `K` than `z₀`, with a uniform margin `d > 0`. -/
def PolePush (K : Set ℂ) (b z₀ : ℂ) : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ z ∈ K, ‖z₀ - b‖ + d ≤ ‖(z : ℂ) - b‖

/-- The partial sums of the Laurent expansion of `z ↦ (z - z₀)⁻¹` in powers of `(z - b)⁻¹`: the
rational functions `R` of lecture 13 p.4, and the approximants produced by the Cauchy transform of
the segment `[z₀, b]`. -/
def laureanSum (z₀ b : ℂ) (K : Set ℂ) (N : ℕ) : ↥K → ℂ :=
  fun z ↦ ∑ k ∈ Finset.range (N + 1), (z₀ - b) ^ k * (((z : ℂ) - b)⁻¹) ^ (k + 1)

/-- The partial sums of the Laurent expansion belong to `PoleAt b K`: they are polynomials in
`z ↦ (z - b)⁻¹`, which is exactly what "the only pole is `b`" means in `Conway.PoleAt`. -/
theorem laureanSum_mem (z₀ b : ℂ) (N : ℕ) : laureanSum z₀ b K N ∈ PoleAt b K := by
  have h : laureanSum z₀ b K N =
      fun z : ↥K ↦ ∑ k ∈ Finset.range (N + 1), (z₀ - b) ^ k * invSub b K z ^ (k + 1) := by
    funext z
    rfl
  rw [h]
  exact mem_PoleAt_sum _ (fun k ↦ (z₀ - b) ^ k) (fun k ↦ k + 1) b

/-- The estimate for the pole pushing lemma: the error of the Laurent partial sums is bounded by a
geometric term, uniform on `K`: this is the "normally convergent" series of lecture 13 p.4. -/
theorem norm_invSub_sub_laureanSum_le {z₀ b : ℂ} {d : ℝ} (hd : 0 < d)
    (hz : ∀ z ∈ K, ‖z₀ - b‖ + d ≤ ‖(z : ℂ) - b‖) (z : ↥K) (N : ℕ) :
    ‖invSub z₀ K z - laureanSum z₀ b K N z‖ ≤
      (‖z₀ - b‖ / (‖z₀ - b‖ + d / 2)) ^ (N + 1) / (d / 2) := by
  have h1 : invSub z₀ K z - laureanSum z₀ b K N z =
      -(((z₀ : ℂ) - (z : ℂ))⁻¹ + laureanSum z₀ b K N z) := by
    change ((z : ℂ) - z₀)⁻¹ - laureanSum z₀ b K N z =
      -(((z₀ : ℂ) - (z : ℂ))⁻¹ + laureanSum z₀ b K N z)
    rw [show (z : ℂ) - z₀ = -((z₀ : ℂ) - (z : ℂ)) by ring, ← neg_inv]
    abel
  have hkey := norm_invSub_add_geom_sum_le (A := (z₀ : ℂ) - b) (B := (z : ℂ) - b)
    (r := ‖(z₀ : ℂ) - b‖) (ρ := ‖(z₀ : ℂ) - b‖ + d / 2) (norm_nonneg _) (le_refl _)
    (by linarith) (by linarith [hz z z.2]) N
  have h2 : ((z₀ : ℂ) - b) - ((z : ℂ) - b) = (z₀ : ℂ) - (z : ℂ) := by ring
  rw [h2, add_tsub_cancel_left] at hkey
  rw [h1, norm_neg]
  exact hkey

/-- **The pole pushing lemma** (lecture 14 p.3-4): if the pole `z₀` of the generator
`z ↦ (z - z₀)⁻¹` can be pushed to `b`, then `z ↦ (z - z₀)⁻¹` is the uniform limit on `K` of the
partial sums of its Laurent expansion in powers of `(z - b)⁻¹`, i.e. it can be approximated by
functions whose only pole is `b`. -/
theorem approximable_PoleAt_of_polePush (hp : PolePush K b z₀) :
    Approximable (PoleAt b K) (invSub z₀ K) := by
  obtain ⟨d, hd, hz⟩ := hp
  have hρ0 : (0 : ℝ) < ‖(z₀ : ℂ) - b‖ + d / 2 := by linarith [norm_nonneg ((z₀ : ℂ) - b)]
  have hq0 : (0 : ℝ) ≤ ‖(z₀ : ℂ) - b‖ / (‖(z₀ : ℂ) - b‖ + d / 2) :=
    div_nonneg (norm_nonneg _) (le_of_lt hρ0)
  have hq1 : ‖(z₀ : ℂ) - b‖ / (‖(z₀ : ℂ) - b‖ + d / 2) < 1 :=
    (div_lt_one hρ0).mpr (by linarith)
  have hconv : TendstoUniformOn K (fun N z ↦ laureanSum z₀ b K N z) (invSub z₀ K) := by
    intro ε ε0
    obtain ⟨N, hN⟩ := exists_pow_mul_lt (ε := ε) (C := (d / 2)⁻¹) hq0 hq1 ε0
    refine ⟨N, fun n hn z ↦ ?_⟩
    have h1 := norm_invSub_sub_laureanSum_le hd hz z n
    have h2 : (‖(z₀ : ℂ) - b‖ / (‖(z₀ : ℂ) - b‖ + d / 2)) ^ (n + 1) / (d / 2) =
        (‖(z₀ : ℂ) - b‖ / (‖(z₀ : ℂ) - b‖ + d / 2)) ^ (n + 1) * (d / 2)⁻¹ := div_eq_mul_inv _ _
    rw [h2] at h1
    rw [norm_sub_rev]
    exact h1.trans_lt (hN (n + 1) (by linarith))
  refine tendstoUniformlyOn_approximable hconv (fun N ↦ ?_)
  exact approximable_of_mem _ (laureanSum_mem z₀ b N)

/-- The partial sums of the Taylor expansion of `z ↦ (z - z₀)⁻¹` about `a`:
`∑ₖ₌₀^N (z - a)^k (z₀ - a)^(-k-1)`, which are *polynomials* in `z`.  The lecturer obtains the case
`w = ∞` of the pole pushing lemma from these. -/
def taylorSum (z₀ a : ℂ) (K : Set ℂ) (N : ℕ) : ↥K → ℂ :=
  fun z ↦ ∑ k ∈ Finset.range (N + 1), ((z : ℂ) - a) ^ k * ((z₀ - a)⁻¹) ^ (k + 1)

/-- The Taylor partial sums are polynomial functions on `K`. -/
theorem taylorSum_mem (z₀ a : ℂ) (N : ℕ) : taylorSum z₀ a K N ∈ Polys K := by
  have h2 : taylorSum z₀ a K N = ∑ k ∈ Finset.range (N + 1),
      (fun z : ↥K ↦ ((z : ℂ) - a) ^ k * ((z₀ - a)⁻¹) ^ (k + 1)) := by
    ext z
    simp only [taylorSum, Finset.sum_apply]
  rw [h2]
  refine Subalgebra.sum_mem _ (fun k _ ↦ ?_)
  have h3 : (fun z : ↥K ↦ ((z : ℂ) - a) ^ k * ((z₀ - a)⁻¹) ^ (k + 1)) =
      ((z₀ - a)⁻¹) ^ (k + 1) • (fun z : ↥K ↦ ((z : ℂ) - a) ^ k) := by
    ext z
    simp [mul_comm]
  rw [h3]
  exact (Polys K).smul_mem (Polys.pow_sub_algebraMap_mem a k) _

/-- The algebraic identity behind the Taylor expansion: `1 / (z - z₀)` plus
`Σₖ (z - a)^k (z₀ - a)^(-k-1)` is the geometric remainder. -/
theorem taylorSum_eq (z₀ a : ℂ) {K : Set ℂ} {R ρ : ℝ} (hR0 : 0 ≤ R)
    (hRK : ∀ z ∈ K, ‖(z : ℂ) - a‖ ≤ R) (hRρ : R < ρ) (hρ : ρ ≤ ‖z₀ - a‖) (z : ↥K) (N : ℕ) :
    invSub z₀ K z + taylorSum z₀ a K N z =
      (((z : ℂ) - a) * (z₀ - a)⁻¹) ^ (N + 1) * ((z : ℂ) - z₀)⁻¹ := by
  have hB : (z₀ : ℂ) - a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hρ
    linarith
  have hAB : ((z : ℂ) - a) - (z₀ - a) ≠ 0 := by
    intro h
    have h1 : (z : ℂ) - a = z₀ - a := sub_eq_zero.mp h
    have h2 : ‖(z₀ : ℂ) - a‖ ≤ R := by rw [← h1]; exact hRK z z.2
    linarith
  have h5 := invSub_geom_sum_eq ((z : ℂ) - a) (z₀ - a) N hB hAB
  rw [show ((z : ℂ) - a) - (z₀ - a) = (z : ℂ) - z₀ by ring] at h5
  change ((z : ℂ) - z₀)⁻¹ + taylorSum z₀ a K N z = _
  exact h5.symm

/-- The case `w = ∞` of the pole pushing lemma, in the form the lecturer uses it (lecture 14 p.3):
if `K ⊆ closedBall a R` and `R < ρ ≤ ‖z₀ - a‖`, then `z ↦ (z - z₀)⁻¹` is the uniform limit on `K`
of the polynomials `z ↦ -Σₖ (z - a)^k (z₀ - a)^(-k-1)`, i.e. the pole `z₀` is replaced by `∞`. -/
theorem approximable_Polys_of_ball {z₀ a : ℂ} {R ρ : ℝ} (hR0 : 0 ≤ R)
    (hRK : ∀ z ∈ K, ‖(z : ℂ) - a‖ ≤ R) (hRρ : R < ρ) (hρ : ρ ≤ ‖z₀ - a‖) :
    Approximable (Polys K) (invSub z₀ K) := by
  have hρ0 : (0 : ℝ) < ρ := by linarith [norm_nonneg (z₀ - a)]
  have hq0 : (0 : ℝ) ≤ R / ρ := div_nonneg hR0 (le_of_lt hρ0)
  have hq1 : R / ρ < 1 := (div_lt_one hρ0).mpr hRρ
  have hconv : TendstoUniformOn K (fun N z ↦ -taylorSum z₀ a K N z) (invSub z₀ K) := by
    intro ε ε0
    obtain ⟨N, hN⟩ := exists_pow_mul_lt (ε := ε) (C := (ρ - R)⁻¹) hq0 hq1 ε0
    refine ⟨N, fun n hn z ↦ ?_⟩
    have h1 : ‖invSub z₀ K z + taylorSum z₀ a K n z‖ ≤ (R / ρ) ^ (n + 1) * (ρ - R)⁻¹ := by
      rw [taylorSum_eq (z₀ := z₀) (a := a) hR0 hRK hRρ hρ z n]
      exact norm_taylor_geom_sum_le hR0 (hRK z z.2) hRρ hρ n
    change ‖(fun N z ↦ -taylorSum z₀ a K N z) n z - invSub z₀ K z‖ < ε
    rw [norm_sub_rev, sub_neg_eq_add]
    exact h1.trans_lt (hN (n + 1) (by linarith))
  refine tendstoUniformlyOn_approximable hconv (fun N ↦ ?_)
  convert Approximable.neg (approximable_of_mem _ (taylorSum_mem z₀ a N)) using 1

/-! ## Chains of pole pushings -/

/-- `ValidPole K w`: the formal pole `w : Option ℂ` — `none` being `∞` — is not on `K`, i.e. it is
either `∞` or a finite point of `Kᶜ`.  Every chain of pole pushings has a valid end point
(`validPole_of_poleChain`), which is what makes its target algebra consist of bounded functions. -/
def ValidPole (K : Set ℂ) (w : Option ℂ) : Prop :=
  match w with
  | none => True
  | some w => w ∉ K

theorem validPole_none : ValidPole K none := trivial
theorem validPole_some {w : ℂ} (hw : w ∉ K) : ValidPole K (some w) := hw

/-- `Target K w`: the algebra of rational functions on `K` with only one pole at the formal point
`w : Option ℂ`, where `none` is `∞`: `PoleAt w K` for a finite `w` (lecture 14 p.3: "rational
functions with only one pole at `w`"), and `Polys K` for `w = ∞` (lecture 14 p.3: "rational
functions with pole only at `w = ∞`", i.e. the partial sums of a power series). -/
def Target (K : Set ℂ) (w : Option ℂ) : Subalgebra ℂ (↥K → ℂ) :=
  match w with
  | none => Polys K
  | some w => PoleAt w K

@[simp] theorem target_none (K : Set ℂ) : Target K none = Polys K := rfl
@[simp] theorem target_some (K : Set ℂ) (w : ℂ) : Target K (some w) = PoleAt w K := rfl

/-- **Chains of pole pushings** (lecture 14 p.3, the proof of the "Hence pole pushing lemma").

`PoleChain K z₀ w` says that the pole of the generator `z ↦ (z - z₀)⁻¹` can be moved to the formal
point `w : Option ℂ` (`none` = `∞`) by finitely many pole pushing steps, so that `invSub z₀ K` can
be approximated on `K` by members of `Target K w`:

* `endF`: no pushing at all, the pole is already a point `z₀ ∉ K`;
* `endT`: the pole is replaced by `∞` using the Taylor expansion
  (`Conway.approximable_Polys_of_ball`); this is the lecturer's "if `w = ∞`, then choose `a ∈ ℂ` and
  `R > 0` such that `K ⊂ B(a;R)` and `z₀ ∉ B(a;R)`.  Then the power series expansion of `f` centered
  at `a` converges normally on compact `K`, so the partial sums — which are polynomials — converge
  to `f` uniformly on `K`";
* `push`: one pole pushing step (`Conway.approximable_PoleAt_of_polePush`), i.e. one segment
  `[z₀, b]` of the polygonal path `γ`, of length `< δ := d(K, γ)`;
* `trans`: concatenation of two chains, i.e. following `γ = γ₀ + ⋯ + γₙ` segment by segment. -/
inductive PoleChain (K : Set ℂ) : ℂ → Option ℂ → Prop where
  | endF {z₀ : ℂ} (hz₀ : z₀ ∉ K) : PoleChain K z₀ (some z₀)
  | endT {z₀ a : ℂ} (R ρ : ℝ) (hR : 0 ≤ R) (hRK : ∀ z ∈ K, ‖(z : ℂ) - a‖ ≤ R)
      (hRρ : R < ρ) (hρ : ρ ≤ ‖z₀ - a‖) : PoleChain K z₀ none
  | push {z₀ b : ℂ} {w : Option ℂ} (hb : PoleChain K b w) (hp : PolePush K b z₀) :
      PoleChain K z₀ w
  | trans {z₀ b : ℂ} {w : Option ℂ} (h1 : PoleChain K z₀ (some b)) (h2 : PoleChain K b w) :
      PoleChain K z₀ w

/-- The end point of a chain of pole pushings is a valid pole: this is the "(∞ not allowed)" remark
of the lecturer's pole pushing lemma, and the reason why `Target K w ≤ BoundedAlg K`. -/
theorem validPole_of_poleChain {z₀ : ℂ} {w : Option ℂ} (hc : PoleChain K z₀ w) :
    ValidPole K w := by
  induction hc with
  | @endF z₀ hz₀ => exact hz₀
  | endT R ρ hR hRK hRρ hρ => exact trivial
  | @push z₀ b w hb hp ih => exact ih
  | @trans z₀ b w h1 h2 _ ih2 => exact ih2

/-- The target algebra of a chain of pole pushings consists of bounded functions on `K`: the
generators `z ↦ (z - a)⁻¹` have their pole off the compact set `K`. -/
theorem PoleChain.target_le_boundedAlg (hK : IsCompact K) {z₀ : ℂ} {w : Option ℂ}
    (hc : PoleChain K z₀ w) : Target K w ≤ BoundedAlg K := by
  cases w with
  | none => rw [target_none]; exact Polys.le_boundedAlg hK
  | some w =>
      rw [target_some]
      exact PoleAt.le_boundedAlg hK (validPole_of_poleChain hc)

/-- **The partial fractions step** (lecture 14 p.2, "by partial fractions expansion and Lemma 0 we
may assume further that `f ∈ ℂ(z)` has only one pole `z₀`") in the form used by the chain induction:
if the generator `z ↦ (z - b)⁻¹` is the uniform limit on `K` of members of the algebra `A`, then so
is every rational function whose only pole is `b` — i.e. every `c / (z - b) ^ n` — provided `A`
consists of bounded functions, so that `Approximable A` is an algebra (Lemma 0). -/
theorem Approximable.all_poleAt {A : Subalgebra ℂ (↥K → ℂ)} (hA : A ≤ BoundedAlg K)
    {b : ℂ} (hb : Approximable A (invSub b K)) : ∀ g ∈ PoleAt b K, Approximable A g := by
  have hsb : PoleAt b K ≤ approximableSubalgebra A hA :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hb)
  intro g hg
  exact hsb hg

/-- **The pole pushing lemma along a chain** (lecture 14 p.3): if the pole of `z ↦ (z - z₀)⁻¹` can
be pushed to the formal point `w` by a chain of pole pushings, then `z ↦ (z - z₀)⁻¹` is the uniform
limit on `K` of rational functions with only one pole at `w`, i.e. of members of `Target K w`.

The two inductive steps are the lecturer's "this is proved by induction on the number of segments of
the polygonal path `γ` using the pole pushing lemma": `Approximable.all_poleAt` is the partial
fractions / Lemma 0 step that lifts the approximation of the single generator `z ↦ (z - b)⁻¹` to all
of `PoleAt b K`, and `Approximable.trans` is Lemma 1. -/
theorem PoleChain.approximable (hK : IsCompact K) {z₀ : ℂ} {w : Option ℂ}
    (hc : PoleChain K z₀ w) : Approximable (Target K w) (invSub z₀ K) := by
  induction hc with
  | @endF z₀ hz₀ =>
      rw [target_some]
      exact approximable_of_mem _ (PoleAt.mem_of_mem z₀)
  | endT R ρ hR hRK hRρ hρ =>
      rw [target_none]
      exact approximable_Polys_of_ball hR hRK hRρ hρ
  | @push z₀ b w hb hp ih =>
      refine Approximable.trans ?_ (approximable_PoleAt_of_polePush hp)
      exact ih.all_poleAt (hb.target_le_boundedAlg hK)
  | @trans z₀ b w h1 h2 ih1 ih2 =>
      rw [target_some] at ih1
      refine Approximable.trans ?_ ih1
      exact ih2.all_poleAt (h2.target_le_boundedAlg hK)

/-- Once the pole has been pushed outside a closed disc that contains `K`, the Taylor
expansion about the centre of the disc replaces the pole by `∞`.

This is the correct form of the lecturer's case `w = ∞` (lecture 14 p.3): the hypothesis
"`K ⊂ B(a;R)` and `z₀ ∉ B(a;R)`" does not hold for an arbitrary `z₀` in the unbounded component
of `ℂ∞ − K` (think of `K` the union of two closed discs and `z₀` in between them), but first
pushing the pole out of `B̄(a;R)` and then expanding does give the `w = ∞` case: see
`poleChain_none_of_unbounded`. -/
theorem PoleChain.push_to_infinity {z₀ b a : ℂ} {R : ℝ} (hc : PoleChain K z₀ (some b))
    (hRK : ∀ z ∈ K, ‖(z : ℂ) - a‖ ≤ R) (hR : 0 ≤ R) (hRb : R < ‖b - a‖) :
    PoleChain K z₀ none :=
  PoleChain.trans hc
    (PoleChain.endT R ((R + ‖b - a‖) / 2) hR hRK (by linarith) (by linarith))

/-- **Axiom: the components of the complement of a compact set are polygonally connected** (a
theorem of the topology of the plane: the open mapping theorem, equivalently invariance of domain).

It is the only topological input to the pole pushing argument, and it is exactly what the lecturer
uses without proof on lecture 14 p.3: "since `U ⊆ ℂ∞` is locally path connected, we can join
`z₀` to
`w` by a polygonal path `γ` in `U`.  Let `δ := d(K, γ) > 0`.  Write `γ = γ₀ + ⋯ + γₙ`
as a finite sum of straight line segments `γⱼ = [zⱼ, zⱼ₊₁]` in `U`, each of length `< δ`".
Indeed the component `U` of `Kᶜ` is *open* (invariance of domain), hence path connected and
even polygonally connected;
`d(K, γ) > 0` because `K` is compact and disjoint from the polygon `γ`; each segment
`[zⱼ, zⱼ₊₁] ⊆ γ` is then at distance at least `δ` from `K` while `‖zⱼ₊₁ - zⱼ‖ < δ`, which says
precisely that `δ ≤ ‖k - zⱼ₊₁‖` for `k ∈ K`, i.e. `Conway.PolePush K zⱼ₊₁ zⱼ`.  The chain of these
pushings is `PoleChain K z₀ (some w)`. -/
axiom exists_poleChain_of_sameComponent (hK : IsCompact K) {z₀ w : ℂ} (hz₀ : z₀ ∉ K)
    (hw : w ∉ K) (h : connectedComponentIn Kᶜ z₀ = connectedComponentIn Kᶜ w) :
    PoleChain K z₀ (some w)

/-- **Pushing a pole to `∞` in the unbounded component of `Kᶜ`**, i.e. in the component of
`ℂ∞ − K` that contains `∞`: the pole is first pushed outside a disc containing `K` and the Taylor
expansion then replaces it by `∞` (`PoleChain.push_to_infinity`).  This is the lecturer's case
`w = ∞` of the "Hence pole pushing lemma" (lecture 14 p.3). -/
theorem poleChain_none_of_unbounded (hK : IsCompact K) {z₀ : ℂ} (hz₀ : z₀ ∉ K)
    (h : ¬BoundedSet (connectedComponentIn Kᶜ z₀)) : PoleChain K z₀ none := by
  obtain ⟨R, hR, hRK⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ K, ‖(z : ℂ)‖ ≤ R := by
    obtain ⟨C, hC0, hC⟩ := boundedOn_coord hK
    exact ⟨C, hC0, fun z hz ↦ hC ⟨z, hz⟩⟩
  obtain ⟨b, hb, hbR⟩ : ∃ b ∈ connectedComponentIn Kᶜ z₀, R + ‖z₀‖ + 1 ≤ ‖b‖ := by
    by_contra h1
    push Not at h1
    exact h ⟨R + ‖z₀‖ + 1, h1⟩
  have hbK : b ∉ K := by simpa using connectedComponentIn_subset Kᶜ z₀ hb
  have h1 : connectedComponentIn Kᶜ z₀ = connectedComponentIn Kᶜ b := connectedComponentIn_eq hb
  refine (exists_poleChain_of_sameComponent hK hz₀ hbK h1).push_to_infinity (a := 0) ?_ hR ?_
  · intro z hz
    simpa using hRK z hz
  · have h2 : R < ‖(b : ℂ)‖ := by linarith [norm_nonneg (z₀ : ℂ)]
    simpa using h2
end

end Conway

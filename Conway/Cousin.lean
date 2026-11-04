/-
Copyright (c) 2026 MA5217 formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MA5217 formalization project (Conway, Chapter VIII)
-/

module

public import Conway.Main

/-!
# The Additive Cousin Problem (Conway VIII.5.2, lecture 16 p.2-3)

Two special cases of the Additive Cousin Problem, exactly as the lecturer states them before the
general Mittag-Leffler theorem (lecture 16 p.2):

* **finite pole set**: `f (z) := Σ_{p ∈ P} f_p (1 / (z − p))` is a solution
  (`Conway.isCousinSolution_of_finite`);
* **adding finitely many principal parts**: if `P₀ ⊆ P` is finite and `f` solves the problem for
  `P − P₀`, then `f + Σ_{p ∈ P₀} f_p (1 / (z − p))` solves it for `P`
  (`Conway.add_finite_cousinSolution`);
* **uniqueness**: two solutions differ by a function holomorphic on all of `G`
  (`Conway.sub_cousinSolution`);
* **compact `G`** (lecture 16 p.3, the Riemann sphere `ℂ∞`): the pole set of a Cousin problem in a
  compact open set is finite, so the explicit finite sum already solves it
  (`Conway.exists_cousinSolution_of_isCompact`).

The lecture also says "interpret `1 / (z − ∞)` as `z`" for a pole at infinity; like the rest of
this formalization, pole sets here live in `ℂ` and the point at infinity is handled by explicit
cases (`Conway.atInfinity`), so no pole-at-infinity term appears.
-/

open Set Filter Topology Polynomial

@[expose] public section

noncomputable section

namespace Conway

variable {G P : Set ℂ} {pp : ℂ → Polynomial ℂ} {p q : ℂ}

/-- `cousinSum s pp` is the finite sum `Σ_{p ∈ s} pp p (1 / (z − p))` of lecture 16 p.2: the
explicit solution of the Additive Cousin Problem when the pole set is finite. -/
def cousinSum (s : Finset ℂ) (pp : ℂ → Polynomial ℂ) : ℂ → ℂ :=
  fun z ↦ ∑ p ∈ s, principalPart pp p z

theorem cousinSum_apply (s : Finset ℂ) (pp : ℂ → Polynomial ℂ) (z : ℂ) :
    cousinSum s pp z = ∑ p ∈ s, principalPart pp p z := rfl

/-- The finite sum of principal parts is holomorphic wherever none of its poles lie. -/
theorem differentiableOn_cousinSum (s : Finset ℂ) (pp : ℂ → Polynomial ℂ) (t : Set ℂ)
    (ht : ∀ p ∈ s, ∀ z ∈ t, z ≠ p) : DifferentiableOn ℂ (cousinSum s pp) t := by
  have h1 : DifferentiableOn ℂ (∑ p ∈ s, principalPart pp p) t :=
    DifferentiableOn.sum fun p hp z hz =>
      (differentiableAt_principalPart pp p z (ht p hp z hz)).differentiableWithinAt
  have h2 : cousinSum s pp = ∑ p ∈ s, principalPart pp p := by
    funext z
    exact (Finset.sum_apply z s (fun p => principalPart pp p)).symm
  rw [h2]
  exact h1

/-- A positive distance from `p` to the finitely many points of `s` other than `p` itself. -/
theorem exists_dist_le_of_mem_erase (s : Finset ℂ) (p : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ s.erase p, δ ≤ ‖(p : ℂ) - q‖ := by
  by_cases hne : s.erase p = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro q hq
    exact absurd hq (by rw [hne]; exact Finset.notMem_empty q)
  · set d : Finset ℝ := (s.erase p).image (fun q => ‖(p : ℂ) - q‖)
    have hdne : d.Nonempty :=
      Finset.Nonempty.image (Finset.nonempty_iff_ne_empty.mpr hne) (fun q => ‖(p : ℂ) - q‖)
    refine ⟨d.min' hdne, ?_, ?_⟩
    · obtain ⟨q, hq, hq2⟩ := Finset.mem_image.mp (Finset.min'_mem d hdne)
      have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
      have hpos : 0 < ‖(p : ℂ) - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hqp))
      rw [← hq2]
      exact hpos
    · intro q hq
      exact Finset.min'_le d _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)

/-- If `δ` is a lower bound for the distances from `p` to the points of `s`, then the ball
`ball p δ` misses `s`: the elementary separation of a finite set from a point. -/
theorem mem_ball_ne (s : Finset ℂ) (p : ℂ) (δ : ℝ)
    (hd : ∀ q ∈ s, δ ≤ ‖(p : ℂ) - q‖) (z : ℂ) (hz : z ∈ Metric.ball p δ) (q : ℂ) (hq : q ∈ s) :
    z ≠ q := by
  intro hqe
  have h1 : dist q p < δ := by
    have h : dist z p < δ := Metric.mem_ball.mp hz
    rwa [hqe] at h
  have h2 : dist q p = ‖(p : ℂ) - q‖ := by rw [Complex.dist_eq, norm_sub_rev]
  exact lt_irrefl _ (h1.trans_le ((hd q hq).trans (le_of_eq h2.symm)))

/-- Subtracting the principal part at `p` from a finite Cousin sum leaves the sum over the other
poles (lecture 16 p.2). -/
theorem subPrincipalPart_cousinSum (s : Finset ℂ) (pp : ℂ → Polynomial ℂ) (p : ℂ) (hp : p ∈ s) :
    (fun z ↦ cousinSum s pp z - principalPart pp p z) =
      fun z ↦ ∑ q ∈ s.erase p, principalPart pp q z := by
  funext z
  have h1 : ∑ q ∈ s, principalPart pp q z =
      principalPart pp p z + ∑ q ∈ s.erase p, principalPart pp q z := by
    rw [add_comm, Finset.sum_erase_add s (fun q => principalPart pp q z) hp]
  rw [cousinSum_apply, h1]
  ring

/-- Near a pole `p` of the finite sum, subtracting the principal part at `p` leaves a function that
is holomorphic on a neighbourhood of `p` (lecture 16 p.2). -/
theorem differentiableOn_subPrincipalPart_cousinSum (s : Finset ℂ) (pp : ℂ → Polynomial ℂ)
    (p : ℂ) (hp : p ∈ s) :
    ∃ δ, 0 < δ ∧
      DifferentiableOn ℂ (fun z ↦ cousinSum s pp z - principalPart pp p z) (Metric.ball p δ) := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_dist_le_of_mem_erase s p
  refine ⟨δ, hδ0, ?_⟩
  rw [subPrincipalPart_cousinSum s pp p hp]
  exact differentiableOn_cousinSum (s.erase p) pp (Metric.ball p δ)
    fun q hq z hz => mem_ball_ne (s.erase p) p δ hδ z hz q hq

/-- A finite Cousin sum is holomorphic near a point which is not one of its poles. -/
theorem exists_ball_diffOn_cousinSum (s : Finset ℂ) (pp : ℂ → Polynomial ℂ) (p : ℂ)
    (hp : p ∉ (s : Set ℂ)) :
    ∃ δ, 0 < δ ∧ DifferentiableOn ℂ (cousinSum s pp) (Metric.ball p δ) := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_dist_le_of_mem_erase s p
  refine ⟨δ, hδ0, differentiableOn_cousinSum s pp (Metric.ball p δ) fun q hq z hz => ?_⟩
  have hqp : q ≠ p := fun h => hp (h ▸ hq)
  exact mem_ball_ne (s.erase p) p δ hδ z hz q (Finset.mem_erase.mpr ⟨hqp, hq⟩)

/-- `a + b − c = (a − c) + b`, applied pointwise to functions. -/
theorem Pi_sub_add (f g pp : ℂ → ℂ) : (fun z ↦ (f + g) z - pp z) = fun z ↦ (f z - pp z) + g z := by
  funext z
  simp only [Pi.add_apply]
  ring

/-- `a + b − c = a + (b − c)`, applied pointwise to functions. -/
theorem Pi_add_sub (f g pp : ℂ → ℂ) : (fun z ↦ (f + g) z - pp z) = fun z ↦ f z + (g z - pp z) := by
  funext z
  simp only [Pi.add_apply]
  ring

/-- **The Additive Cousin Problem for a finite pole set** (Conway VIII.5.2, lecture 16 p.2): "if
`P` is finite, then `f (z) := Σ_{p ∈ P} f_p (1 / (z − p))` is a solution". -/
theorem isCousinSolution_of_finite (hG : IsOpen G) (hPG : P ⊆ G) (s : Finset ℂ)
    (hs : (s : Set ℂ) = P) (pp : ℂ → Polynomial ℂ) :
    IsCousinSolution G P pp (cousinSum s pp) := by
  have hmem (w : ℂ) : w ∈ (s : Set ℂ) ↔ w ∈ P := by rw [hs]
  refine ⟨differentiableOn_cousinSum s pp (G \ P) fun p hp z hz hqe =>
      hz.2 (hqe.symm ▸ (hmem p).mp hp), ?_⟩
  · intro p hp
    obtain ⟨δ₁, hδ₁0, hb1⟩ := IsOpen.exists_ball_subset hG p (hPG hp)
    obtain ⟨δ₂, hδ₂0, h2⟩ :=
      differentiableOn_subPrincipalPart_cousinSum s pp p ((hmem p).mpr hp)
    refine ⟨min δ₁ δ₂, lt_min hδ₁0 hδ₂0, ?_, ?_⟩
    · exact (Metric.ball_subset_ball (min_le_left δ₁ δ₂)).trans hb1
    · exact h2.mono (Metric.ball_subset_ball (min_le_right δ₁ δ₂))

/-- **Adding finitely many principal parts** (lecture 16 p.2, "more generally…"): if `P₀` is a
finite subset of the pole set `P` and `f` solves the Cousin problem for `P − P₀`, then
`f + Σ_{p ∈ P₀} f_p (1 / (z − p))` solves it for `P`.  That the point `p ∈ P₀` is isolated in `P`
(which comes from `hP : NoAccumulationIn P G`) is what makes `f` holomorphic near `p`. -/
theorem add_finite_cousinSolution (hG : IsOpen G) (hPG : P ⊆ G) (hP : NoAccumulationIn P G)
    (s : Finset ℂ) (hsP : (s : Set ℂ) ⊆ P) (pp : ℂ → Polynomial ℂ) (f : ℂ → ℂ)
    (hf : IsCousinSolution G (P \ (s : Set ℂ)) pp f) :
    IsCousinSolution G P pp (f + cousinSum s pp) := by
  refine ⟨(hf.1.mono (sdiff_subset_sdiff (Subset.refl G) sdiff_subset)).add ?_, ?_⟩
  · exact differentiableOn_cousinSum s pp (G \ P) fun p hp z hz hqe =>
      hz.2 (by rw [hqe]; exact hsP hp)
  · intro p hp
    obtain ⟨δ₁, hδ₁0, hb1⟩ := IsOpen.exists_ball_subset hG p (hPG hp)
    by_cases hps : p ∈ (s : Set ℂ)
    · -- the pole `p` lies in `P₀`: its principal part cancels and `f` itself is holomorphic
      -- near `p`, because `p` is isolated in `P`
      obtain ⟨δ₂, hδ₂0, h2⟩ := differentiableOn_subPrincipalPart_cousinSum s pp p hps
      obtain ⟨δ₃, hδ₃0, hiso⟩ := hP p (hPG hp)
      have hball : Metric.ball p (min δ₁ (min δ₂ δ₃)) ⊆ Metric.ball p δ₃ :=
        Metric.ball_subset_ball (min_le_right δ₁ (min δ₂ δ₃) |>.trans (min_le_right δ₂ δ₃))
      have hg : Metric.ball p (min δ₁ (min δ₂ δ₃)) ⊆ G :=
        (Metric.ball_subset_ball (min_le_left δ₁ (min δ₂ δ₃))).trans hb1
      have hc : ∀ z ∈ Metric.ball p (min δ₁ (min δ₂ δ₃)), z ∉ P \ (s : Set ℂ) := by
        intro z hz hzP
        have hzp : z = p := hiso ⟨hball hz, hzP.1⟩
        exact hzP.2 (hzp ▸ hps)
      have hf' : DifferentiableOn ℂ f (Metric.ball p (min δ₁ (min δ₂ δ₃))) := by
        refine hf.1.mono ?_
        intro z hz
        exact ⟨hg hz, hc z hz⟩
      refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁0 (lt_min hδ₂0 hδ₃0), hg, ?_⟩
      have h2' : DifferentiableOn ℂ (fun z ↦ cousinSum s pp z - principalPart pp p z)
          (Metric.ball p (min δ₁ (min δ₂ δ₃))) :=
        h2.mono (Metric.ball_subset_ball (min_le_right δ₁ (min δ₂ δ₃) |>.trans
          (min_le_left δ₂ δ₃)))
      rw [Pi_add_sub]
      exact hf'.add h2'
    · -- the pole `p` lies in `P − P₀`: the solution `f` takes care of it near `p`
      obtain ⟨δ₂, hδ₂0, h2⟩ := exists_ball_diffOn_cousinSum s pp p hps
      obtain ⟨δ₃, hδ₃0, hb3, h3⟩ := hf.2 p ⟨hp, hps⟩
      refine ⟨min δ₂ δ₃, lt_min hδ₂0 hδ₃0,
        (Metric.ball_subset_ball (min_le_right δ₂ δ₃)).trans hb3, ?_⟩
      rw [Pi_sub_add]
      exact (h3.mono (Metric.ball_subset_ball (min_le_right δ₂ δ₃))).add
        (h2.mono (Metric.ball_subset_ball (min_le_left δ₂ δ₃)))

/-- **The uniqueness part of the Additive Cousin Problem** (lecture 16 p.2): two solutions of the
same Cousin problem differ by a function that is holomorphic on all of `G`. -/
theorem sub_cousinSolution (hG : IsOpen G) (hP : IsClosed P) {f g : ℂ → ℂ}
    (hf : IsCousinSolution G P pp f) (hg : IsCousinSolution G P pp g) :
    DifferentiableOn ℂ (fun z ↦ g z - f z) G := by
  intro z hz
  by_cases hzP : z ∈ P
  · obtain ⟨δ, hδ0, _, hfd⟩ := hf.2 z hzP
    obtain ⟨δ', hδ'0, _, hgd⟩ := hg.2 z hzP
    have hη0 : 0 < min δ δ' := lt_min hδ0 hδ'0
    have hfd' : DifferentiableOn ℂ (fun w : ℂ => f w - principalPart pp z w)
        (Metric.ball z (min δ δ')) :=
      hfd.mono (Metric.ball_subset_ball (min_le_left δ δ'))
    have hgd' : DifferentiableOn ℂ (fun w : ℂ => g w - principalPart pp z w)
        (Metric.ball z (min δ δ')) :=
      hgd.mono (Metric.ball_subset_ball (min_le_right δ δ'))
    have heq : (fun w : ℂ => g w - f w) =
        (fun w : ℂ => g w - principalPart pp z w) -
          (fun w : ℂ => f w - principalPart pp z w) := by
      funext w
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    exact ((hgd'.sub hfd').differentiableAt (Metric.ball_mem_nhds z hη0)).differentiableWithinAt
  · have hopen : IsOpen (G \ P) := hG.sdiff hP
    have hnhds : (G \ P) ∈ 𝓝 z := hopen.mem_nhds ⟨hz, hzP⟩
    have hdiff : DifferentiableAt ℂ (fun w : ℂ => g w - f w) z :=
      (hg.1.differentiableAt hnhds).sub (hf.1.differentiableAt hnhds)
    exact hdiff.differentiableWithinAt

/-- Lecture 16 p.2: "since `G` is second countable, the set `P` is at most countable".  For a plane
domain the second countability is used through the compact exhaustion `Conway.exh` of lecture 15
p.1: `P` is the union of the countably many finite sets `exh G n ∩ P`. -/
theorem NoAccumulationIn.countable (hG : IsOpen G) (hPG : P ⊆ G) (hP : NoAccumulationIn P G) :
    P.Countable := by
  refine Set.Countable.mono ?_ (Set.countable_iUnion fun n =>
    (hP.inter_isFinite (isCompact_exh n) exh_subset_G).countable)
  intro z hz
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (subset_iUnion_exh hG (hPG hz))
  exact Set.mem_iUnion.mpr ⟨n, ⟨hn, hz⟩⟩

/-- Lecture 16 p.3: a Cousin problem whose pole set lies in a compact subset of `G` is solved by
the explicit finite sum of principal parts.  This is why the Mittag-Leffler theorem on the compact
Riemann sphere `ℂ∞` needs no approximation argument: there every pole set is finite. -/
theorem exists_cousinSolution_of_isCompact (hG : IsOpen G) (hGc : IsCompact G) (hPG : P ⊆ G)
    (hP : NoAccumulationIn P G) (pp : ℂ → Polynomial ℂ) : ∃ f, IsCousinSolution G P pp f := by
  obtain ⟨s, hs⟩ : ∃ s : Finset ℂ, (s : Set ℂ) = P := by
    have hfin : P.Finite :=
      Set.Finite.subset (hP.inter_isFinite (K := G) hGc (Subset.refl G))
        (Set.subset_inter hPG (Subset.refl P))
    exact ⟨hfin.toFinset, hfin.coe_toFinset⟩
  exact ⟨cousinSum s pp, isCousinSolution_of_finite hG hPG s hs pp⟩

end Conway

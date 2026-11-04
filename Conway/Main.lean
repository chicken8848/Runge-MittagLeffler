/-
Copyright (c) 2026 MA5217 formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MA5217 formalization project (Conway, Chapter VIII)
-/

module

public import Conway.Exhaustion
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Analysis.Complex.SummableUniformlyOn

/-!
# The Mittag-Leffler theorem (Conway VIII.5.2, lectures 16 and 17)

This is the lecturer's own proof (lecture 16 p.2-3):

* the poles of `Fₙ` are exactly the poles of `P` that enter at step `n` of the compact exhaustion
  `Kₙ = Conway.exh G n` of `G` (lecture 16 p.2), so all of them lie outside `Kₙ`;
* Runge's theorem (`Conway.runge'`), applied to `Fₙ` on `Kₙ` with pole set `E = ℂ − G` — the
  topological hypothesis holds because `ℂ∞ − Kₙ` is connected, `Conway.meetsComponents_exh` —
  gives rational functions `Rₙ`, holomorphic on `G`, with
  `|Fₙ − Rₙ| < (1/2)^(n+1)` on `Kₙ`;
* `f = Σₙ (Fₙ − Rₙ)` converges locally uniformly off `P`, hence is holomorphic on `ℂ − P`
  (Weierstrass' theorem, `SummableLocallyUniformlyOn.differentiableOn`);
* near a pole `p` only one `Fₙ` contributes, so `f − pp_p` is a locally uniform limit of functions
  holomorphic near `p`.

The hypothesis "P has no accumulation points in G" is `Conway.NoAccumulationIn` and the principal
part at `p` is `Conway.principalPart pp p : ℂ → ℂ`, the polynomial `pp p` evaluated at
`1 / (z − p)`, which is exactly `Σⱼ cⱼ / (z − p)^{#ⱼ}` of the notes (Conway VIII.5.1).
-/

open Set Filter Topology Polynomial

@[expose] public section

noncomputable section

namespace Conway

variable {G P : Set ℂ} {E : Set ℂ} {atInfinity : Bool} {pp : ℂ → Polynomial ℂ} {p q : ℂ}
variable {n m : ℕ} {α : Type} {A : ℕ → Set α} {x : α}

/-! ## The hypothesis on the polar set -/

/-- `NoAccumulationIn P G`: no point of `G` is an accumulation point of the polar set `P`; this is
the hypothesis "P has no accumulation points in G" of the Mittag-Leffler theorem (Conway VIII.5.2,
lecture 16 p.2). -/
def NoAccumulationIn (P G : Set ℂ) : Prop :=
  ∀ z ∈ G, ∃ δ, 0 < δ ∧ Metric.ball z δ ∩ P ⊆ {z}

theorem NoAccumulationIn.mono (hP : NoAccumulationIn P G) (hHG : H ⊆ G) :
    NoAccumulationIn P H := fun z hz ↦
  let ⟨δ, δ0, hδ⟩ := hP z (hHG hz)
  ⟨δ, δ0, hδ⟩

theorem NoAccumulationIn.erase (hP : NoAccumulationIn P G) : NoAccumulationIn (P \ {p}) G :=
  fun z hz ↦
    let ⟨δ, δ0, hδ⟩ := hP z hz
    ⟨δ, δ0, (inter_subset_inter_right _ sdiff_subset).trans hδ⟩

/-- A set with no accumulation point in `G` meets every compact subset of `G` in a finite set:
this is the form of the hypothesis used repeatedly in the lecture (lecture 16 p.2). -/
theorem NoAccumulationIn.inter_isFinite (hP : NoAccumulationIn P G) {K : Set ℂ}
    (hK : IsCompact K) (hKG : K ⊆ G) : (K ∩ P).Finite := by
  choose r hr using fun (i : ↥G) => hP i.1 i.2
  have hcov : K ⊆ ⋃ i : ↥G, Metric.ball (i : ℂ) (r i) := by
    intro z hz
    refine Set.mem_iUnion.mpr ⟨⟨z, hKG hz⟩, ?_⟩
    refine Metric.mem_ball.mpr ?_
    rw [dist_self]
    exact (hr ⟨z, hKG hz⟩).1
  obtain ⟨t, hsub⟩ := hK.elim_finite_subcover (fun i : ↥G => Metric.ball (i : ℂ) (r i))
    (fun _ ↦ Metric.isOpen_ball) hcov
  refine ((Finset.finite_toSet t).image (fun i : ↥G => (i : ℂ))).subset ?_
  rintro w ⟨hwK, hwP⟩
  obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.mp (hsub hwK)
  have hw : w = (i : ℂ) := (hr i).2 ⟨hwi, hwP⟩
  subst hw
  exact ⟨i, hi, rfl⟩

/-! ## The principal part -/

/-- `principalPart pp p` is the principal part with pole at `p` with coefficients from the
polynomial `pp p`: `z ↦ pp p (1 / (z − p))`, i.e. `Σⱼ cⱼ / (z − p)^{#ⱼ}` of the notes.  Its only
singularity is `p`, where its value is `0` (`1 / 0 = 0` by convention in Lean). -/
def principalPart (pp : ℂ → Polynomial ℂ) (p : ℂ) : ℂ → ℂ :=
  fun z ↦ (pp p).eval ((z - p)⁻¹)

theorem principalPart_apply (pp : ℂ → Polynomial ℂ) (p z : ℂ) :
    principalPart pp p z = (pp p).eval ((z - p)⁻¹) := rfl

theorem differentiableAt_principalPart (pp : ℂ → Polynomial ℂ) (p z : ℂ) (hz : z ≠ p) :
    DifferentiableAt ℂ (principalPart pp p) z := by
  have h1 : DifferentiableAt ℂ (fun y : ℂ ↦ (pp p).eval y) ((z - p)⁻¹) :=
    Polynomial.differentiableAt _
  have h2 : DifferentiableAt ℂ (fun w : ℂ ↦ (w - p)⁻¹) z :=
    (((hasDerivAt_id' z).sub (hasDerivAt_const z p)).inv (sub_ne_zero.mpr hz)).differentiableAt
  exact DifferentiableAt.comp z h1 h2

/-- The principal part with pole `p` is holomorphic on any set not containing `p` (lecture 16 p.1:
a principal part is a rational function whose only pole is `p`). -/
theorem differentiableOn_principalPart (s : Set ℂ) (pp : ℂ → Polynomial ℂ) (p : ℂ)
    (hs : ∀ z ∈ s, z ≠ p) : DifferentiableOn ℂ (principalPart pp p) s :=
  fun z hz ↦ (differentiableAt_principalPart pp p z (hs z hz)).differentiableWithinAt

/-- A principal part is holomorphic off its pole. -/
theorem differentiableOn_principalPart_ne (pp : ℂ → Polynomial ℂ) (p : ℂ) :
    DifferentiableOn ℂ (principalPart pp p) {z | z ≠ p} :=
  differentiableOn_principalPart {z | z ≠ p} pp p fun _ hz ↦ hz

/-! ## The Cousin solution -/

/-- `IsCousinSolution G P pp f`: the function whose existence is asserted by the Mittag-Leffler
theorem (Conway VIII.5.2, lecture 16 p.2): `f` is holomorphic on `G` outside `P`, and near each
`p ∈ P` the difference of `f` with the principal part `pp p` is holomorphic. -/
def IsCousinSolution (G P : Set ℂ) (pp : ℂ → Polynomial ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (G \ P) ∧
    ∀ p ∈ P, ∃ δ, 0 < δ ∧ Metric.ball p δ ⊆ G ∧
      DifferentiableOn ℂ (fun z ↦ f z - principalPart pp p z) (Metric.ball p δ)

/-! ## The poles that enter at step `n` (lecture 16 p.2) -/

/-- `Conway.polesOn hP n` is the finite set `P ∩ Kₙ` of lecture 16 p.2: only finitely many poles
lie in a compact subset of `G`, because `P` has no accumulation point in `G`. -/
noncomputable def polesOn (hP : Conway.NoAccumulationIn P G) (n : ℕ) : Finset ℂ :=
  (hP.inter_isFinite (Conway.isCompact_exh n) Conway.exh_subset_G).toFinset

theorem mem_polesOn (hP : Conway.NoAccumulationIn P G) (n : ℕ) (z : ℂ) :
    (z ∈ (polesOn hP n : Set ℂ)) ↔ z ∈ Conway.exh G n ∧ z ∈ P := by
  simp only [polesOn, Set.Finite.coe_toFinset, Set.mem_inter_iff]

/-- The sets `P ∩ Kₙ` are increasing, because the exhaustion `Kₙ` is. -/
theorem polesOn_subset (hP : Conway.NoAccumulationIn P G) {n m : ℕ} (h : n ≤ m) :
    (polesOn hP n : Set ℂ) ⊆ (polesOn hP m : Set ℂ) := by
  intro z hz
  obtain ⟨h1, h2⟩ := (mem_polesOn hP n z).mp hz
  exact (mem_polesOn hP m z).mpr ⟨Conway.exh_mono h h1, h2⟩

/-- Every pole of `P` lies in `P ∩ Kₙ` for `n` large enough: the polar set is exhausted by the `Kₙ`
(lecture 16 p.2, where `G = ⋃ₙ Kₙ` is used). -/
theorem exists_mem_polesOn (hG : IsOpen G) (hPG : P ⊆ G)
    (hP : Conway.NoAccumulationIn P G) (z : ℂ) (hz : z ∈ P) : ∃ n, z ∈ (polesOn hP n : Set ℂ) := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (Conway.subset_iUnion_exh hG (hPG hz))
  exact ⟨n, (mem_polesOn hP n z).mpr ⟨hn, hz⟩⟩

/-- The shells of an increasing sequence of sets: an element of the union belongs to exactly one
shell.  This is the combinatorics behind "each pole is a pole of exactly one `Fₙ`". -/
theorem exists_unique_mem_shells (hA : ∀ n m : ℕ, n ≤ m → A n ⊆ A m) {s : Set α}
    (hU : ∀ x ∈ s, ∃ n, x ∈ A n) {x : α} (hx : x ∈ s) :
    ∃! n, (x ∈ A (n + 1) ∧ (n = 0 ∨ x ∉ A n)) := by
  classical
  set m := Nat.find (hU x hx) with hm
  have hIn : x ∈ A m := Nat.find_spec (hU x hx)
  have hlt : ∀ k, k < m → x ∉ A k := fun k hk ↦ Nat.find_min (hU x hx) hk
  have key : ∀ n : ℕ, (x ∈ A (n + 1) ∧ (n = 0 ∨ x ∉ A n)) ↔ n = m - 1 := by
    intro n
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : m ≤ n + 1 := by
        by_contra h3
        exact hlt (n + 1) (by omega) h1
      cases h2 with
      | inl h0 =>
        subst h0
        omega
      | inr hnp =>
        have h4 : n < m := by
          by_contra h4
          exact hnp (hA m n (by omega) hIn)
        omega
    · intro h
      refine ⟨hA m (n + 1) (by omega) hIn, ?_⟩
      by_cases hn : n = 0
      · exact Or.inl hn
      · refine Or.inr (hlt n ?_)
        omega
  refine ⟨m - 1, (key (m - 1)).mpr rfl, fun n hn ↦ (key n).mp hn⟩

/-- The poles of `Fₙ`: `P ∩ Kₙ₊₁ − P ∩ Kₙ` (lecture 16 p.2, "let `Fₙ` be the sum of the principal
parts of the poles in `Kₙ₊₁ − Kₙ`"), the case `n = 0` taking care of the poles that already lie in
`K₀`. -/
noncomputable def newPoles (hP : Conway.NoAccumulationIn P G) (n : ℕ) : Finset ℂ :=
  polesOn hP (n + 1) \ if n = 0 then ∅ else polesOn hP n

theorem mem_newPoles (hP : Conway.NoAccumulationIn P G) (n : ℕ) (z : ℂ) :
    (z ∈ (newPoles hP n : Set ℂ)) ↔
      (z ∈ (polesOn hP (n + 1) : Set ℂ)) ∧ (n = 0 ∨ z ∉ (polesOn hP n : Set ℂ)) := by
  cases n with
  | zero => simp [newPoles]
  | succ n => simp [newPoles]

/-- Each pole is a pole of exactly one `Fₙ`: the partition of the polar set that the lecturer uses
when saying that, near a pole, only one term `Fₙ` is singular (lecture 16 p.3). -/
theorem exists_unique_mem_newPoles (hG : IsOpen G) (hPG : P ⊆ G)
    (hP : Conway.NoAccumulationIn P G) (p : ℂ) (hp : p ∈ P) :
    ∃! n, p ∈ (newPoles hP n : Set ℂ) := by
  obtain ⟨n₀, hn₀, huniq⟩ :=
    exists_unique_mem_shells (A := fun n ↦ (polesOn hP n : Set ℂ)) (fun n m h ↦
      polesOn_subset hP h) (fun z hz ↦ exists_mem_polesOn hG hPG hP z hz) hp
  refine ⟨n₀, ?_, fun m hm ↦ ?_⟩
  · exact (mem_newPoles hP n₀ p).mpr hn₀
  · exact huniq m ((mem_newPoles hP m p).mp hm)

/-- The poles of `Fₙ` are poles: they lie in `P`. -/
theorem newPoles_subset (hP : Conway.NoAccumulationIn P G) (n : ℕ) :
    (newPoles hP n : Set ℂ) ⊆ P := by
  intro z hz
  have h1 : z ∈ (polesOn hP (n + 1) : Set ℂ) := (Finset.mem_sdiff.mp hz).1
  exact ((mem_polesOn hP (n + 1) z).mp h1).2

/-- None of the poles of `Fₙ` lies in `Kₙ`, for `n > 0`: this is why `Fₙ` is holomorphic near `Kₙ`,
the compact set that Runge's theorem is applied to (lecture 16 p.2).  The term `F₀` collects the
poles that are already in `K₁`, and it is dealt with by taking `R₀ = 0`. -/
theorem not_mem_newPoles (hP : Conway.NoAccumulationIn P G) {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z ∈ Conway.exh G n) : z ∉ (newPoles hP n : Set ℂ) := by
  intro h
  obtain ⟨h1, h2⟩ := (mem_newPoles hP n z).mp h
  cases h2 with
  | inl h0 => exact absurd h0 (Nat.ne_of_gt hn)
  | inr hnp =>
    have hP' : z ∈ P := ((mem_polesOn hP (n + 1) z).mp h1).2
    exact hnp ((mem_polesOn hP n z).mpr ⟨hz, hP'⟩)

/-- `G − P` is open (lecture 16 p.3, where the series is shown to converge in `ℂ − P`): a set
without accumulation points in `G` is closed relative to `G`. -/
theorem isOpen_sdiff_poles (hG : IsOpen G) (hP : Conway.NoAccumulationIn P G) :
    IsOpen (G \ P) :=
  isOpen_iff_mem_nhds.mpr fun z hz ↦ by
    obtain ⟨δ, δ0, hδ⟩ := hP z hz.1
    have hsub : Metric.ball z δ ⊆ Pᶜ := fun w hw hwp ↦ hz.2
      (by have := hδ ⟨hw, hwp⟩; subst this; exact hwp)
    exact inter_mem (hG.mem_nhds hz.1) (mem_of_superset (Metric.ball_mem_nhds z δ0) hsub)

/-- `G − (P − {p})` is open (lecture 16 p.3). -/
theorem isOpen_sdiff_poles_erase (hG : IsOpen G) (hP : Conway.NoAccumulationIn P G) (p : ℂ) :
    IsOpen (G \ (P \ {p})) :=
  isOpen_iff_mem_nhds.mpr fun z hz ↦ by
    obtain ⟨δ, δ0, hδ⟩ := hP z hz.1
    have hsub : Metric.ball z δ ⊆ (P \ {p})ᶜ := fun w hw hwp ↦ hz.2
      (by have := hδ ⟨hw, hwp.1⟩; subst this; exact hwp)
    exact inter_mem (hG.mem_nhds hz.1) (mem_of_superset (Metric.ball_mem_nhds z δ0) hsub)

/-! ## The functions `Fₙ` of lecture 16 p.2 -/

/-- `Conway.cousinTerm pp hP n` is the function `Fₙ` of lecture 16 p.2: the sum of the principal
parts of the poles that enter at step `n` of the exhaustion,
`Fₙ(z) = Σ_{p ∈ P ∩ Kₙ₊₁ − Kₙ} pp p (1 / (z − p))`. -/
noncomputable def cousinTerm (pp : ℂ → Polynomial ℂ) (hP : Conway.NoAccumulationIn P G)
    (n : ℕ) : ℂ → ℂ :=
  ∑ w ∈ newPoles hP n, Conway.principalPart pp w

theorem cousinTerm_apply (pp : ℂ → Polynomial ℂ) (hP : Conway.NoAccumulationIn P G) (n : ℕ)
    (z : ℂ) : cousinTerm pp hP n z = ∑ w ∈ newPoles hP n, Conway.principalPart pp w z :=
  Finset.sum_apply z (newPoles hP n) (fun w ↦ Conway.principalPart pp w)

/-- `Fₙ` is holomorphic off its poles, which are the points of `P` that enter at step `n`: in
particular it is holomorphic near `Kₙ` (lecture 16 p.2), and on `G − P`. -/
theorem differentiableOn_cousinTerm (pp : ℂ → Polynomial ℂ)
    (hP : Conway.NoAccumulationIn P G) (n : ℕ) {s : Set ℂ}
    (hs : ∀ z ∈ s, z ∉ (newPoles hP n : Set ℂ)) :
    DifferentiableOn ℂ (cousinTerm pp hP n) s := by
  refine DifferentiableOn.sum fun w hw ↦ Conway.differentiableOn_principalPart s pp w ?_
  intro z hz hEq
  subst hEq
  exact hs z hz hw

/-- The version used near a pole `p`: erasing `p` from the poles of `Fₙ` gives the function
`Fₙ − pp p` of lecture 16 p.3, which is holomorphic at `p`. -/
noncomputable def cousinDiffAt (pp : ℂ → Polynomial ℂ) (hP : Conway.NoAccumulationIn P G)
    (p : ℂ) (n : ℕ) : ℂ → ℂ :=
  ∑ w ∈ newPoles hP n \ {p}, Conway.principalPart pp w

theorem cousinDiffAt_apply (pp : ℂ → Polynomial ℂ) (hP : Conway.NoAccumulationIn P G) (p : ℂ)
    (n : ℕ) (z : ℂ) :
    cousinDiffAt pp hP p n z = ∑ w ∈ newPoles hP n \ {p}, Conway.principalPart pp w z :=
  Finset.sum_apply z (newPoles hP n \ {p}) (fun w ↦ Conway.principalPart pp w)

/-- `Fₙ − pp p` is holomorphic at `p` (lecture 16 p.3). -/
theorem differentiableOn_cousinDiffAt (pp : ℂ → Polynomial ℂ)
    (hP : Conway.NoAccumulationIn P G) (p : ℂ) (n : ℕ) {s : Set ℂ}
    (hs : ∀ z ∈ s, z ∉ ((newPoles hP n \ {p} : Finset ℂ) : Set ℂ)) :
    DifferentiableOn ℂ (cousinDiffAt pp hP p n) s := by
  refine DifferentiableOn.sum fun w hw ↦ Conway.differentiableOn_principalPart s pp w ?_
  intro z hz hEq
  subst hEq
  exact hs z hz hw

/-- Removing the principal part at `p` from `Fₙ`: the identity that turns the series
`Σ (Fₙ − Rₙ)` into a series of functions holomorphic at `p` (lecture 16 p.3). -/
theorem sub_principalPart_cousinTerm (pp : ℂ → Polynomial ℂ)
    (hP : Conway.NoAccumulationIn P G) (p : ℂ) (n : ℕ) :
    (fun z ↦ cousinTerm pp hP n z -
        (if p ∈ (newPoles hP n : Set ℂ) then Conway.principalPart pp p z else 0)) =
      cousinDiffAt pp hP p n := by
  funext z
  by_cases hmem : p ∈ (newPoles hP n : Set ℂ)
  · have hif : (if p ∈ (newPoles hP n : Set ℂ) then Conway.principalPart pp p z else 0) =
      Conway.principalPart pp p z := by simp [hmem]
    rw [hif, cousinTerm_apply, cousinDiffAt_apply]
    have hsub : ({p} : Finset ℂ) ⊆ newPoles hP n := Finset.singleton_subset_iff.mpr hmem
    rw [← Finset.sum_sdiff hsub, Finset.sum_singleton, add_sub_cancel_right]
  · have hif : (if p ∈ (newPoles hP n : Set ℂ) then Conway.principalPart pp p z else 0) = 0 :=
      by simp [hmem]
    have hne : ∀ w ∈ (newPoles hP n : Finset ℂ), ¬ w ∈ ({p} : Finset ℂ) := by
      intro w hw h2
      exact hmem (Finset.mem_singleton.mp h2 ▸ hw)
    have hset : newPoles hP n \ ({p} : Finset ℂ) = newPoles hP n :=
      Finset.ext fun w ↦
        ⟨fun h ↦ (Finset.mem_sdiff.mp h).1,
          fun h ↦ Finset.mem_sdiff.mpr ⟨h, hne w h⟩⟩
    rw [hif, sub_zero, cousinTerm_apply, cousinDiffAt_apply, hset]

/-- The error tolerance `εₙ = (1/2)^(n+1)` of lecture 16 p.3, where Runge's theorem is applied with
this `ε`. -/
noncomputable def cousinEps (n : ℕ) : ℝ := ((1 : ℝ) / 2) ^ (n + 1)

theorem cousinEps_pos (n : ℕ) : 0 < cousinEps n := pow_pos (by norm_num) _

theorem summable_cousinEps : Summable cousinEps := by
  have h1 : cousinEps = fun n ↦ ((1 : ℝ) / 2) * ((1 : ℝ) / 2) ^ n := by
    funext n
    simp only [cousinEps]
    rw [show ((1 : ℝ) / 2) ^ (n + 1) = (1 / 2) * (1 / 2) ^ n by rw [pow_succ]; ring]
  rw [h1]
  exact Summable.mul_left _ (summable_geometric_of_norm_lt_one (by norm_num))

/-! ## The functions `Rₙ` of lecture 16 p.3: Runge's theorem applied to `Fₙ` -/

/-- A ball inside an open set (the `ball p δ ⊆ G` of lecture 16 p.3). -/
theorem IsOpen.exists_ball_subset (hG : IsOpen G) (z : ℂ) (hz : z ∈ G) :
    ∃ δ, 0 < δ ∧ Metric.ball z δ ⊆ G := Metric.mem_nhds_iff.mp (hG.mem_nhds hz)

/-- The ℂ-subalgebra of `ℂ → ℂ` whose carrier is the set of functions holomorphic on `s`; used to
say that the rational functions of Runge's theorem are holomorphic where their poles are not. -/
def diffOnAlg (s : Set ℂ) : Subalgebra ℂ (ℂ → ℂ) where
  carrier := {f | DifferentiableOn ℂ f s}
  add_mem' := (fun a b (ha : DifferentiableOn ℂ a s) (hb : DifferentiableOn ℂ b s) ↦
      ha.add hb :
      ∀ a b, DifferentiableOn ℂ a s → DifferentiableOn ℂ b s → DifferentiableOn ℂ (a + b) s)
  mul_mem' := (fun a b (ha : DifferentiableOn ℂ a s) (hb : DifferentiableOn ℂ b s) ↦
      ha.mul hb :
      ∀ a b, DifferentiableOn ℂ a s → DifferentiableOn ℂ b s → DifferentiableOn ℂ (a * b) s)
  zero_mem' := differentiableOn_const _
  one_mem' := differentiableOn_const _
  algebraMap_mem' := fun _ ↦ differentiableOn_const _

theorem mem_diffOnAlg {s : Set ℂ} {f : ℂ → ℂ} : f ∈ diffOnAlg s ↔ DifferentiableOn ℂ f s :=
  Iff.rfl

/-- The generators of the algebra `Conway.RatFun E atInfinity` of rational functions with poles in
`E` are holomorphic off `E`. -/
theorem RatFun.diffOnAlg_le {s : Set ℂ} (h : ∀ a ∈ E, ∀ z ∈ s, z ≠ a) :
    RatFun E atInfinity ≤ diffOnAlg s := by
  cases atInfinity with
  | false =>
    rw [RatFun.eq_false]
    refine Algebra.adjoin_le_iff.mpr (Set.image_subset_iff.mpr fun a ha ↦
      mem_diffOnAlg.mpr ((differentiableOn_id.sub (differentiableOn_const _)).inv fun z hz ↦
        sub_ne_zero.mpr (h a ha z hz)))
  | true =>
    rw [RatFun.eq_true]
    refine Algebra.adjoin_le_iff.mpr (Set.union_subset_iff.mpr
      ⟨Set.image_subset_iff.mpr fun a ha ↦
          mem_diffOnAlg.mpr ((differentiableOn_id.sub (differentiableOn_const _)).inv fun z hz ↦
            sub_ne_zero.mpr (h a ha z hz)),
        Set.singleton_subset_iff.mpr (mem_diffOnAlg.mpr differentiableOn_id)⟩)

/-- A rational function with poles in `E` is holomorphic off `E`: applied to the functions `Rₙ` of
lecture 16 p.3, whose poles lie in `ℂ − G`, this says that `Rₙ` is holomorphic in `G`. -/
theorem differentiableOn_of_mem_RatFun {s : Set ℂ} {g : ℂ → ℂ} (hg : g ∈ RatFun E atInfinity)
    (h : ∀ a ∈ E, ∀ z ∈ s, z ≠ a) : DifferentiableOn ℂ g s :=
  mem_diffOnAlg.mp (RatFun.diffOnAlg_le h hg)

/-- Rewriting the approximating function of `Conway.Within`. -/
theorem Within.congr_right {ε : ℝ} {K : Set ℂ} {f g₁ g₂ : ↥K → ℂ} (h : Within K ε f g₁)
    (hEq : ∀ z : ↥K, g₁ z = g₂ z) : Within K ε f g₂ := fun z ↦ by rw [← hEq z]; exact h z

/-- **The approximation step** (lecture 16 p.3: "by Runge's theorem there is a rational function
`Rₙ`, holomorphic in `G`, with `|Fₙ(z) − Rₙ(z)| < (1/2)^(n+1)` on `Kₙ`"): `Fₙ` is holomorphic on
`G − {its poles}`, which is open and contains `Kₙ` (`Conway.not_mem_newPoles`), and the pole set
`E = ℂ − G` satisfies the topological hypothesis of Runge's theorem because `ℂ∞ − Kₙ` is connected
(`Conway.meetsComponents_exh`).  The term `F₀`, whose poles need not avoid `K₀`, is left out: it is
a single term and does not affect the convergence of the series. -/
theorem exists_cousin_R (hG : IsOpen G) (pp : ℂ → Polynomial ℂ) (hP : NoAccumulationIn P G) :
    ∃ R : ℕ → ℂ → ℂ, (∀ n, DifferentiableOn ℂ (R n) G) ∧
      ∀ n, 0 < n → Within (exh G n) (cousinEps n)
        (fun z : ↥(exh G n) ↦ cousinTerm pp hP n z) (fun z : ↥(exh G n) ↦ R n z) := by
  have h1 : ∀ n : ℕ, ∃ g ∈ RatFun Gᶜ true,
      0 < n → Within (exh G n) (cousinEps n)
        (fun z : ↥(exh G n) ↦ cousinTerm pp hP n z) (fun z : ↥(exh G n) ↦ g z) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨0, Subalgebra.zero_mem _, fun hnpos ↦ absurd hnpos (Nat.lt_irrefl 0)⟩
    · obtain ⟨R, hR, hWithin⟩ :=
        runge' (E := Gᶜ) (atInfinity := true) (K := exh G n) (G := G \ (newPoles hP n : Set ℂ))
          (isCompact_exh n)
          (hG.sdiff (Finset.finite_toSet _).isClosed)
          (fun z hz ↦ ⟨exh_subset_G hz, not_mem_newPoles hP hn hz⟩)
          (fun a ha hK ↦ ha (exh_subset_G hK))
          (meetsComponents_exh (Or.inl rfl) (meetsComponents_complement G))
          (cousinTerm pp hP n)
          (differentiableOn_cousinTerm pp hP n fun z hz ↦ hz.2)
          (cousinEps n) (cousinEps_pos n)
      obtain ⟨g, hg, hge⟩ := exists_ratFun_of_mem_RatAlgOn (E := Gᶜ) (atInfinity := true) hR
      refine ⟨g, hg, fun _ ↦ Within.congr_right hWithin fun z ↦ (hge z).symm⟩
  choose R hR using h1
  refine ⟨R, ?_, ?_⟩
  · intro n
    exact differentiableOn_of_mem_RatFun (hR n).1 fun a ha z hz hEq ↦
      ha (by rw [← hEq]; exact hz)
  · intro n hn
    exact (hR n).2 hn

/-! ## The series `Σ (Fₙ − Rₙ)` of lecture 16 p.3 converges locally uniformly -/

/-- The tolerances `εₙ = (1/2)^(n+1)` of lecture 16 p.3 are decreasing. -/
theorem cousinEps_le (n : ℕ) : cousinEps (n + 1) ≤ cousinEps n := by
  have h1 : cousinEps (n + 1) = cousinEps n * (1 / 2 : ℝ) := by
    change ((1 : ℝ) / 2) ^ (n + 1 + 1) = ((1 : ℝ) / 2) ^ (n + 1) * (1 / 2 : ℝ)
    rw [pow_succ]
  rw [h1]
  linarith [cousinEps_pos n]

/-- Erasing the principal part at `p` from `Fₙ` does nothing when `p` is not a pole of `Fₙ`: this is
how the estimate of Runge's theorem is transferred to the series of lecture 16 p.3 near `p`. -/
theorem cousinDiffAt_eq_cousinTerm (pp : ℂ → Polynomial ℂ) (hP : NoAccumulationIn P G) (p : ℂ)
    (n : ℕ) (hp : p ∉ (newPoles hP n : Set ℂ)) (z : ℂ) :
    cousinDiffAt pp hP p n z = cousinTerm pp hP n z := by
  have h1 := congrFun (sub_principalPart_cousinTerm pp hP p n) z
  rw [← h1]
  simp [hp]

/-- The point form of `Conway.sub_principalPart_cousinTerm`, in the direction used to compare the
terms `Fₙ − Rₙ` and `Fₙ − pp p − Rₙ` of lecture 16 p.3. -/
theorem sub_principalPart_cousinTerm_apply (pp : ℂ → Polynomial ℂ)
    (hP : NoAccumulationIn P G) (p : ℂ) (n : ℕ) (z : ℂ) :
    cousinTerm pp hP n z =
      cousinDiffAt pp hP p n z +
        (if p ∈ (newPoles hP n : Set ℂ) then principalPart pp p z else 0) := by
  have h1 := congrFun (sub_principalPart_cousinTerm pp hP p n) z
  rw [← h1]
  abel

/-- The poles of `Fₙ − pp p` are poles of `Fₙ` other than `p`. -/
theorem mem_newPoles_erase {hP : NoAccumulationIn P G} {p : ℂ} {n : ℕ} {w : ℂ}
    (hw : w ∈ ((newPoles hP n \ {p} : Finset ℂ) : Set ℂ)) : w ∈ P ∧ w ≠ p := by
  obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hw
  refine ⟨newPoles_subset hP n h1, ?_⟩
  intro hEq
  exact h2 (hEq ▸ Finset.mem_singleton_self p)

/-- **The M-test of lecture 16 p.3**: if the terms are eventually bounded by the tolerance `εₙ` on
the compact set `Kₙ` of the exhaustion, then their series converges locally uniformly on every open
subset of `G`, because every compact subset of `G` is contained in some `Kₙ`
(`Conway.exists_interior_exh_subset`). -/
theorem summableLocallyUniformlyOn_exh (hG : IsOpen G) {g : ℕ → ℂ → ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hsubs : s ⊆ G)
    (h : ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → ∀ z ∈ exh G m, ‖g m z‖ ≤ cousinEps m) :
    SummableLocallyUniformlyOn g s := by
  obtain ⟨n₀, hn₀⟩ := h
  refine SummableLocallyUniformlyOn.of_locally_bounded_eventually hs ?_
  intro K hKs hKc
  obtain ⟨n₁, hn₁⟩ := exists_interior_exh_subset hG hKc (hKs.trans hsubs)
  refine ⟨cousinEps, summable_cousinEps, ?_⟩
  filter_upwards [Finset.eventually_cofinite_notMem (Finset.range (max n₀ n₁))] with m hm z hz
  have hge : max n₀ n₁ ≤ m := Nat.le_of_not_lt fun hlt ↦ hm (Finset.mem_range.mpr hlt)
  exact hn₀ m (le_trans (Nat.le_max_left _ _) hge) z
    (exh_mono (le_trans (Nat.le_max_right _ _) hge) (interior_subset (hn₁ hz)))

/-- The series `Σ (Fₙ − Rₙ)` of lecture 16 p.3 converges locally uniformly in `G − P`; the term
`F₀` is kept in front of the series (see `Conway.exists_cousin_R`), which is why the estimate of
Runge's theorem is needed from the index `1` on. -/
theorem summableLocallyUniformlyOn_cousin (hG : IsOpen G) (pp : ℂ → Polynomial ℂ)
    (hP : NoAccumulationIn P G) (R : ℕ → ℂ → ℂ)
    (hR : ∀ n, 0 < n → Within (exh G n) (cousinEps n)
        (fun z : ↥(exh G n) ↦ cousinTerm pp hP n z) (fun z : ↥(exh G n) ↦ R n z)) :
    SummableLocallyUniformlyOn (fun n ↦ cousinTerm pp hP (n + 1) - R (n + 1)) (G \ P) :=
  summableLocallyUniformlyOn_exh hG (isOpen_sdiff_poles hG hP) sdiff_subset
    ⟨0, fun m _m z hz ↦
      (le_of_lt (hR (m + 1) (Nat.succ_pos m) ⟨z, exh_mono (Nat.le_succ m) hz⟩)).trans
        (cousinEps_le m)⟩

/-- The series of lecture 16 p.3 with the principal part at `p` removed — the series whose sum is
`f − pp p` — converges locally uniformly on every open subset of `G`: this is what makes `f − pp p`
holomorphic at `p`.  The single index at which `p` is a pole of `Fₙ` is absorbed by the `n₀` of the
M-test. -/
theorem summableLocallyUniformlyOn_cousinDiffAt (hG : IsOpen G) (hPG : P ⊆ G)
    (hP : NoAccumulationIn P G) (pp : ℂ → Polynomial ℂ) {p : ℂ} (hp : p ∈ P) (R : ℕ → ℂ → ℂ)
    (hR : ∀ n, 0 < n → Within (exh G n) (cousinEps n)
        (fun z : ↥(exh G n) ↦ cousinTerm pp hP n z) (fun z : ↥(exh G n) ↦ R n z))
    {s : Set ℂ} (hs : IsOpen s) (hsubs : s ⊆ G) :
    SummableLocallyUniformlyOn (fun n ↦ cousinDiffAt pp hP p (n + 1) - R (n + 1)) s := by
  obtain ⟨k, hk, hu⟩ := exists_unique_mem_newPoles hG hPG hP p hp
  refine summableLocallyUniformlyOn_exh hG hs hsubs ⟨k, fun m _m z hz ↦ ?_⟩
  have hpn : p ∉ (newPoles hP (m + 1) : Set ℂ) := by
    intro h
    have h2 : m + 1 = k := hu (m + 1) h
    omega
  calc ‖cousinDiffAt pp hP p (m + 1) z - R (m + 1) z‖
      = ‖cousinTerm pp hP (m + 1) z - R (m + 1) z‖ := by
        rw [cousinDiffAt_eq_cousinTerm pp hP p (m + 1) hpn z]
    _ ≤ cousinEps m :=
      (le_of_lt (hR (m + 1) (Nat.succ_pos m) ⟨z, exh_mono (Nat.le_succ m) hz⟩)).trans
        (cousinEps_le m)

/-- **The Mittag-Leffler theorem** (Conway VIII.5.2, lecture 16 p.2-3): let `G` be an open subset of
`ℂ`, let `P ⊆ G` have no accumulation point in `G`, and let a principal part be prescribed at each
point of `P`.  Then there is a function `f`, holomorphic on `G − P`, whose singular part at each
`p ∈ P` is exactly the prescribed principal part.  The proof is the lecturer's own: `f` is `F₀` plus
the sum of the series `Σₙ (Fₙ₊₁ − Rₙ₊₁)` of lecture 16 p.3, the convergence is the M-test above, and
the holomorphy of `f − pp p` at the pole `p` uses that only one `Fₙ` is singular at `p`. -/
theorem exists_cousin_solution (hG : IsOpen G) (hPG : P ⊆ G) (pp : ℂ → Polynomial ℂ)
    (hP : NoAccumulationIn P G) : ∃ f, IsCousinSolution G P pp f := by
  obtain ⟨R, hR1, hR2⟩ := exists_cousin_R hG pp hP
  let f : ℂ → ℂ := fun z ↦ cousinTerm pp hP 0 z + ∑' n, (cousinTerm pp hP (n + 1) - R (n + 1)) z
  have hfdef : ∀ z, f z = cousinTerm pp hP 0 z + ∑' n, (cousinTerm pp hP (n + 1) - R (n + 1)) z :=
    fun _ ↦ rfl
  have hsum : SummableLocallyUniformlyOn (fun n ↦ cousinTerm pp hP (n + 1) - R (n + 1)) (G \ P) :=
    summableLocallyUniformlyOn_cousin hG pp hP R hR2
  have hd0 : DifferentiableOn ℂ (cousinTerm pp hP 0) (G \ P) :=
    differentiableOn_cousinTerm pp hP 0 fun z hz hw ↦ hz.2 (newPoles_subset hP 0 hw)
  have hds : DifferentiableOn ℂ (fun z ↦ ∑' n, (cousinTerm pp hP (n + 1) - R (n + 1)) z) (G \ P) :=
    SummableLocallyUniformlyOn.differentiableOn (isOpen_sdiff_poles hG hP) hsum fun m z hz ↦
      ((differentiableOn_cousinTerm pp hP (m + 1) (s := G \ P) fun w hw hwP ↦
          hw.2 (newPoles_subset hP (m + 1) hwP)).differentiableAt
            ((isOpen_sdiff_poles hG hP).mem_nhds hz)).sub
          ((hR1 (m + 1)).differentiableAt (hG.mem_nhds hz.1))
  have hf : DifferentiableOn ℂ f (G \ P) := DifferentiableOn.add hd0 hds
  refine ⟨f, hf, ?_⟩
  intro p hp
  obtain ⟨δ, δ0, hδ⟩ := hP p (hPG hp)
  obtain ⟨δ', δ'0, hδ'⟩ := IsOpen.exists_ball_subset hG p (hPG hp)
  obtain ⟨k, hk, hu⟩ := exists_unique_mem_newPoles hG hPG hP p hp
  set η : ℝ := min δ δ' with hη
  have hη0 : 0 < η := lt_min δ0 δ'0
  have hball : Metric.ball p η ⊆ G :=
    fun z hz ↦ hδ' (Metric.ball_subset_ball (min_le_right δ δ') hz)
  have hpole : ∀ z ∈ Metric.ball p η, z ∉ (P \ {p} : Set ℂ) := by
    intro z hz hzP
    obtain ⟨hzP1, hzP2⟩ := hzP
    have h3 : z ∈ ({p} : Set ℂ) :=
      hδ ⟨Metric.ball_subset_ball (min_le_left δ δ') hz, hzP1⟩
    exact hzP2 h3
  have hsum2 : SummableLocallyUniformlyOn
      (fun n ↦ cousinDiffAt pp hP p (n + 1) - R (n + 1)) (Metric.ball p η) :=
    summableLocallyUniformlyOn_cousinDiffAt hG hPG hP pp hp R hR2 Metric.isOpen_ball hball
  have hd1 : DifferentiableOn ℂ (cousinDiffAt pp hP p 0) (Metric.ball p η) :=
    differentiableOn_cousinDiffAt pp hP p 0 fun z hz hw ↦
      hpole z hz ⟨(mem_newPoles_erase hw).1, (mem_newPoles_erase hw).2⟩
  have hd2 : DifferentiableOn ℂ (fun z ↦ ∑' n, (cousinDiffAt pp hP p (n + 1) - R (n + 1)) z)
      (Metric.ball p η) :=
    SummableLocallyUniformlyOn.differentiableOn Metric.isOpen_ball hsum2 fun m z hz ↦
      ((differentiableOn_cousinDiffAt pp hP p (m + 1) fun w hw hwP ↦
          hpole w hw ⟨(mem_newPoles_erase hwP).1, (mem_newPoles_erase hwP).2⟩).differentiableAt
            (Metric.isOpen_ball.mem_nhds hz)).sub ((hR1 (m + 1)).differentiableAt
              (hG.mem_nhds (hball hz)))
  have hterm : ∀ (z : ℂ) (m : ℕ), (cousinTerm pp hP m - R m) z =
      (cousinDiffAt pp hP p m - R m) z +
        (if p ∈ (newPoles hP m : Set ℂ) then principalPart pp p z else 0) := by
    intro z m
    have h1 := sub_principalPart_cousinTerm_apply pp hP p m z
    change cousinTerm pp hP m z - R m z = (cousinDiffAt pp hP p m z - R m z) +
      (if p ∈ (newPoles hP m : Set ℂ) then principalPart pp p z else 0)
    rw [h1]
    abel
  have hEq : ∀ z ∈ Metric.ball p η, f z - principalPart pp p z =
      cousinDiffAt pp hP p 0 z + ∑' n, (cousinDiffAt pp hP p (n + 1) - R (n + 1)) z := by
    intro z hz
    have hb : HasSum (fun n ↦ (cousinDiffAt pp hP p (n + 1) - R (n + 1)) z)
        (∑' n, (cousinDiffAt pp hP p (n + 1) - R (n + 1)) z) :=
      (SummableLocallyUniformlyOn.hasSumLocallyUniformlyOn hsum2).hasSum hz
    by_cases hk0 : k = 0
    · have hnp : ∀ m, 0 < m → p ∉ (newPoles hP m : Set ℂ) := by
        intro m hm hmem
        have h2 : m = k := hu m hmem
        omega
      have hδ0 : HasSum (fun n ↦ (if p ∈ (newPoles hP (n + 1) : Set ℂ)
            then principalPart pp p z else (0 : ℂ))) 0 := by
        refine hasSum_zero.congr_fun fun n ↦ ?_
        simp [hnp (n + 1) (Nat.succ_pos n)]
      have hsum_f := ((hb.add hδ0).congr_fun fun n ↦ hterm z (n + 1)).tsum_eq
      have hbase : cousinTerm pp hP 0 z = cousinDiffAt pp hP p 0 z + principalPart pp p z := by
        have hmem : p ∈ (newPoles hP 0 : Set ℂ) := by
          rw [← hk0]
          exact hk
        have h1 := sub_principalPart_cousinTerm_apply pp hP p 0 z
        have hif : (if p ∈ (newPoles hP 0 : Set ℂ) then principalPart pp p z else 0) =
            principalPart pp p z := by simp [hmem]
        rwa [hif] at h1
      rw [hfdef, hsum_f, hbase]
      abel
    · have hmem0 : p ∉ (newPoles hP 0 : Set ℂ) := by
        intro hmem
        exact hk0 ((hu 0 hmem).symm)
      have hd_eq : ∀ n, (if p ∈ (newPoles hP (n + 1) : Set ℂ) then principalPart pp p z else 0) =
          if n = k - 1 then principalPart pp p z else 0 := by
        intro n
        by_cases hmem : p ∈ (newPoles hP (n + 1) : Set ℂ)
        · have hEqn : n = k - 1 := by
            have hpos : 0 < k := Nat.pos_of_ne_zero hk0
            have h2 : n + 1 = k := hu (n + 1) hmem
            omega
          have hL : (if p ∈ (newPoles hP (n + 1) : Set ℂ) then principalPart pp p z else 0) =
              principalPart pp p z := by simp [hmem]
          have hR : (if n = k - 1 then principalPart pp p z else 0) = principalPart pp p z := by
            simp [hEqn]
          rw [hL, hR]
        · have hne : n ≠ k - 1 := by
            intro hEqn
            have hpos : 0 < k := Nat.pos_of_ne_zero hk0
            have h2 : n + 1 = k := by omega
            exact hmem (by rw [h2]; exact hk)
          have hL : (if p ∈ (newPoles hP (n + 1) : Set ℂ) then principalPart pp p z else 0) = 0 :=
            by simp [hmem]
          have hR : (if n = k - 1 then principalPart pp p z else 0) = 0 := by simp [hne]
          rw [hL, hR]
      have hδ0 : HasSum (fun n ↦ (if p ∈ (newPoles hP (n + 1) : Set ℂ)
            then principalPart pp p z else (0 : ℂ))) (principalPart pp p z) :=
        (hasSum_ite_eq (k - 1) (principalPart pp p z)).congr_fun fun n ↦ hd_eq n
      have hsum_f := ((hb.add hδ0).congr_fun fun n ↦ hterm z (n + 1)).tsum_eq
      have hbase : cousinTerm pp hP 0 z = cousinDiffAt pp hP p 0 z := by
        have h1 := sub_principalPart_cousinTerm_apply pp hP p 0 z
        have hif : (if p ∈ (newPoles hP 0 : Set ℂ) then principalPart pp p z else 0) = 0 := by
          simp [hmem0]
        rwa [hif, add_zero] at h1
      rw [hfdef, hsum_f, hbase]
      abel
  have h2 : DifferentiableOn ℂ
      (fun z ↦ cousinDiffAt pp hP p 0 z +
        ∑' n, (cousinDiffAt pp hP p (n + 1) - R (n + 1)) z) (Metric.ball p η) :=
    DifferentiableOn.add hd1 hd2
  exact ⟨η, hη0, hball, h2.congr hEq⟩

end Conway

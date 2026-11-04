/-
Copyright (c) 2026 MA5217 formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MA5217 formalization project (Conway, Chapter VIII)
-/

module

public import Conway.Cauchy
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# MA5217 / Conway Chapter VIII, §1: the Separation Lemma and the weak Runge theorem

This file contains the top of the lecturer's proof of Runge's theorem (lecture 13 p.2–4): the
"Enhanced Separation Lemma" — the only input from the topology of the plane, i.e. winding numbers
of 1-cycles and the global Cauchy integral formula — and the resulting **weak Runge theorem**,
in which the allowed pole set is the full complement `E = ℂ∞ − K`.

The lecturer's argument and where each step is formalized:

1. "First, apply the Enhanced Separation Lemma to get a 1-cycle `Γ` in `G − K ⊆ G`, consisting of a
   finite number of closed polygons, such that `f(z) = (2πi)⁻¹ ∫_Γ f(w)/(w − z) dw` for all `z ∈ K`"
   — `Conway.enhancedSeparationLemma` below;
2. "Write `Γ = E₁ + ⋯ + Eₙ` as a finite sum of straight line segments `Eⱼ` in `G − K`. Then
   `f(z) = Σⱼ (2πi)⁻¹ ∫_[Eⱼ] f(w)/(w − z) dw =: Σⱼ fⱼ(z)`. It suffices to show the approximation
   claim for each `fⱼ`" — "it suffices" is `Conway.Approximable.sum` (iterated Lemma 0) together
   with `Conway.Approximable.mono`, and the constant `(2πi)⁻¹` is absorbed by
   `Conway.Approximable.const_smul`;
3. "Let `δ := d(K,E) > 0`; write `E = E₁ + ⋯ + Eₙ` where each `Eⱼ` is of length `< δ`. Let `z₀ ∈ E`
   be the midpoint of `E`. Then the closed disc `B̄(z₀; δ/2)`, having `E` as diameter, is disjoint
   from `K`" — `Conway.norm_lineMap_sub_midpoint_le` plus the two `δ`-bounds recorded in the axiom
   (every point of every segment, in particular its midpoint, is `δ`-far from `K`);
4. "The function `z ↦ (2πi)⁻¹ ∫_[E] φ(w)/(w − z) dw` is holomorphic on `ℂ − B̄(z₀; δ/2) =
   ann(z₀; δ/2, ∞)`; consider its Laurent series expansion at `z₀`; the partial sums
   `R(z) = Σ_{n=1}^N a₋ₙ (z − z₀)^(−n)` have a pole at `z₀ ∈ ℂ∞ − K` and converge normally on `K`"
   — `Conway.approximable_segIntegral` (in `Conway/Cauchy.lean`), whose approximants
   `Conway.segApprox` are the partial sums of the geometric-series expansion proved in
   `Conway/Geom.lean`.
-/

@[expose] public section

open scoped BigOperators Convex
open Set Filter AffineMap

namespace Conway

noncomputable section

variable {K G : Set ℂ} {f : ℂ → ℂ}

/-! ## The Separation Lemma: the single axiomatized input -/

/-- **Enhanced Separation Lemma** (lecture 13 p.2, "= Separation Lemma + global Cauchy's integral
formula"; compare Conway VIII.1.1 Proposition, whose proof needs the machinery of 1-cycles and
winding numbers, and Conway VIII.2.2).

Let `K ⊆ G ⊆ ℂ` with `K` compact and `G` open, and let `f` be holomorphic on `G`.  Then there are
`δ > 0` and finitely many straight line segments `[aⱼ, bⱼ]` such that

* the segments lie in `G − K`: `∀ j, [aⱼ, bⱼ] ⊆ G \ K`;
* every point of every segment is at distance `≥ δ` from `K`:
  `∀ j w ∈ [aⱼ, bⱼ] ∀ k ∈ K, δ ≤ ‖w - k‖` (this is `δ ≤ d(K, Γ)`);
* the segments are *short*: `∀ j, ‖bⱼ - aⱼ‖ < 2δ` — this is the lecturer's subdivision step,
  "write `E = E₁ + ⋯ + Eₙ` where each `Eⱼ` is of length `< δ`", which leaves the set traced out by
  the cycle, and hence `d(K, Γ)`, unchanged;
* the global Cauchy integral formula holds on `K`:
  `f(z) = (2πi)⁻¹ Σⱼ ∫_[aⱼ,bⱼ] f(w)/(w − z) dw`, where the integral is written in the parametrized
  form `∫₀¹ f(lineMap a b t) (lineMap a b t − z)⁻¹ (b − a) dt = Conway.segIntegral f a b z`
  (Mathlib's `curveIntegral_segment`).

The two properties that the lecturer's formulation states in terms of winding numbers — the cycle
`Γ` consists of finitely many closed polygons in `G − K` with `n(Γ; w) = 0` for `w ∈ ℂ − G` and
`n(Γ; z) = 1` for `z ∈ K` — are precisely the hypotheses from which the displayed Cauchy
representation is derived (Conway VIII.1.1, VIII.2.2); they are folded into that representation
here because Mathlib v4.35 has no theory of 1-cycles or of the winding number of a cycle.

**This is one of the two axioms of this formalization**: the other one is
`Conway.exists_poleChain_of_sameComponent` in `Conway/PolePushing.lean` (see also the module
doc-string of `Conway/Runge.lean`); everything else in `Conway/` is proved.
-/
axiom enhancedSeparationLemma {K G : Set ℂ} (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f G) :
    ∃ (δ : ℝ) (n : ℕ) (a b : Fin n → ℂ), 0 < δ ∧
      (∀ j : Fin n, segment ℝ (a j) (b j) ⊆ G \ K) ∧
      (∀ (j : Fin n) (w : ℂ), w ∈ segment ℝ (a j) (b j) → ∀ k ∈ K, δ ≤ ‖w - k‖) ∧
      (∀ j : Fin n, ‖b j - a j‖ < 2 * δ) ∧
      ∀ z ∈ K, f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ * ∑ j : Fin n, segIntegral f (a j) (b j) z

/-! ## The midpoint of a segment (lecture 13 p.3) -/

theorem half_mem_Icc : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

/-- The midpoint `lineMap a b (1/2) = (a + b) / 2` of the segment `[a,b]`, as a point of it. -/
theorem midpoint_mem_segment (a b : ℂ) : lineMap a b (1 / 2 : ℝ) ∈ segment ℝ a b := by
  rw [segment_eq_image_lineMap]
  exact mem_image_of_mem _ half_mem_Icc

/-- The difference of two points of a segment: `lineMap a b t - lineMap a b s = (t - s) • (b - a)`.
-/
theorem sub_lineMap_lineMap (a b : ℂ) (s t : ℝ) :
    lineMap a b t - lineMap a b s = (t - s) • (b - a) := by
  rw [lineMap_apply_module', lineMap_apply_module', add_sub_add_right_eq_sub, ← sub_smul]

/-- **The geometry of the midpoint** (lecture 13 p.3): the segment `[a,b]` is contained in the
closed disc of radius `‖b - a‖ / 2` centred at its midpoint — "the closed discs `B̄(z₀; δ/2)` having
`E` as diameter". -/
theorem norm_lineMap_sub_midpoint_le {a b : ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖lineMap a b t - lineMap a b (1 / 2 : ℝ)‖ ≤ ‖b - a‖ / 2 := by
  have h2 : |(t : ℝ) - 1 / 2| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  have h3 : ‖lineMap a b t - lineMap a b (1 / 2 : ℝ)‖ ≤ (1 / 2 : ℝ) * ‖b - a‖ := by
    rw [sub_lineMap_lineMap, norm_smul]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have h4 : (1 / 2 : ℝ) * ‖b - a‖ = ‖b - a‖ / 2 := by ring
  rwa [← h4]

/-! ## The approximation claim for one segment -/

/-- **The "without loss of generality" step** (lecture 13 p.2–4): with the notation of the Enhanced
Separation Lemma, the Cauchy transform of `f` over *one* of the segments, normalizing constant
`(2πi)⁻¹` included, is a uniform limit on `K` of rational functions with a single pole at the
midpoint of that segment:

    fⱼ(z) = (2πi)⁻¹ ∫_[aⱼ,bⱼ] f(w)/(w − z) dw  ≈  Σ_{n=1}^N a₋ₙ (z − z₀)^(−n),   z₀ = midpoint.

The radius bounds are exactly the lecturer's: the segment is contained in `B̄(z₀; ‖b − a‖/2)`, the
midpoint is `δ`-far from `K`, and `‖b − a‖ < 2δ` makes the two discs disjoint with room to spare. -/
theorem approximable_segIntegral_of_separation (δ : ℝ) (_hδ0 : 0 < δ) {a b : ℂ}
    (hsub : segment ℝ a b ⊆ G \ K) (hδ : ∀ w ∈ segment ℝ a b, ∀ k ∈ K, δ ≤ ‖w - k‖)
    (hab : ‖b - a‖ < 2 * δ) (hf : ContinuousOn f G) :
    Approximable (PoleAt (lineMap a b (1 / 2 : ℝ)) K)
      (fun z : ↥K ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * segIntegral f a b z) := by
  have hG : ContinuousOn f [a -[ℝ] b] := hf.mono fun _ hz => (hsub hz).1
  have hr : ∀ t ∈ Icc (0 : ℝ) 1, ‖lineMap a b t - lineMap a b (1 / 2 : ℝ)‖ ≤ ‖b - a‖ / 2 :=
    fun t ht ↦ norm_lineMap_sub_midpoint_le ht
  have hρ : ‖b - a‖ / 2 < δ := by linarith
  have hmid : ∀ k ∈ K, δ ≤ ‖lineMap a b (1 / 2 : ℝ) - k‖ :=
    hδ _ (midpoint_mem_segment a b)
  have hK : ∀ z ∈ K, (‖b - a‖ / 2 + δ) / 2 < ‖(z : ℂ) - lineMap a b (1 / 2 : ℝ)‖ := by
    intro z hz
    have h1 := hmid z hz
    rw [norm_sub_rev] at h1
    linarith
  have h := approximable_segIntegral (hr0 := by positivity) (hr := hr) (hrρ := by linarith)
    (hK := hK) hG
  exact h.const_smul _

/-! ## Weak Runge's theorem -/

/-- **Weak Runge's Theorem** (lecture 13 p.2, the case `E = ℂ∞ − K` of 1.7, where the lecturer
notes that the poles produced are "in `ℂ∞ − K` (not `∞`)").  Let `K ⊆ G ⊆ ℂ` with `K` compact and
`G` open, and let `f` be holomorphic on `G`.  Then `f`, restricted to `K`, is a uniform limit on
`K` of rational functions whose poles lie in `Kᶜ` and with *no polynomial part* (no pole at `∞`):

    Approximable (RatAlg Kᶜ K) (fun z : ↥K ↦ f z),

i.e. for every `ε > 0` there is a rational function `R` with poles only in `Kᶜ ⊆ ℂ∞ − K`, `R`
vanishing at `∞`, such that `|f(z) − R(z)| < ε` uniformly on `K`.

This is the lecturer's proof verbatim: the Enhanced Separation Lemma reduces the claim to the Cauchy
transforms `fⱼ` of single line segments in `G − K` (the "without loss of generality" of lecture 13
p.2, which is `Conway.Approximable.sum` + `Conway.Approximable.const_smul` here), and each `fⱼ` is
approximated by the partial sums of its Laurent expansion at the midpoint `zⱼ` of the segment
(`Conway.approximable_segIntegral_of_separation`); since `‖bⱼ − aⱼ‖ < 2δ ≤ 2 d(K, [aⱼ,bⱼ])` the
midpoint is not in `K`, so `PoleAt zⱼ K ≤ RatAlg Kᶜ K` supplies "poles only in `ℂ∞ − K`, not `∞`".
-/
theorem weakRunge {K G : Set ℂ} (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f G) :
    Approximable (RatAlg Kᶜ K) fun z : ↥K ↦ f z := by
  obtain ⟨δ, n, a, b, hδ0, hsub, hδ, hlen, hrep⟩ :=
    enhancedSeparationLemma hK hG hKG f hf
  have hG' : ContinuousOn f G := hf.continuousOn
  have key : ∀ j : Fin n, Approximable (RatAlg Kᶜ K)
      (fun z : ↥K ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * segIntegral f (a j) (b j) z) := by
    intro j
    have hj : Approximable (PoleAt (lineMap (a j) (b j) (1 / 2 : ℝ)) K)
        (fun z : ↥K ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * segIntegral f (a j) (b j) z) :=
      approximable_segIntegral_of_separation (f := f) (a := a j) (b := b j) δ hδ0
        (hsub j) (hδ j) (hlen j) hG'
    have hjK : lineMap (a j) (b j) (1 / 2 : ℝ) ∉ K := by
      intro hK'
      have h1 := hδ j _ (midpoint_mem_segment _ _) _ hK'
      rw [sub_self, norm_zero] at h1
      linarith
    exact Approximable.mono (PoleAt.le hjK) hj
  have hsum : Approximable (RatAlg Kᶜ K)
      (fun z : ↥K ↦ ∑ j : Fin n, (2 * Real.pi * Complex.I : ℂ)⁻¹ * segIntegral f (a j) (b j) z) :=
    Approximable.sum (s := Finset.univ)
      (F := fun j z ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * segIntegral f (a j) (b j) z)
      (fun j _ ↦ key j)
  have hcong : (fun z : ↥K ↦ ∑ j : Fin n, (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      segIntegral f (a j) (b j) z) = (fun z : ↥K ↦ f z) := by
    refine funext fun z ↦ ?_
    rw [← Finset.mul_sum, hrep z z.2]
  exact hsum.congr hcong

/-- **Weak Runge's Theorem** allowing a pole at `∞` as well; this is `Conway.weakRunge` weakened to
the algebra `RatAlgInf Kᶜ K` used in lecture 14. -/
theorem weakRungeInf {K G : Set ℂ} (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f G) :
    Approximable (RatAlgInf Kᶜ K) fun z : ↥K ↦ f z :=
  (weakRunge hK hG hKG f hf).mono RatAlg.le_RatAlgInf

/-- **Weak Runge's Theorem in the `ε`-form of lecture 13 p.2**: there is a rational function whose
poles lie in `ℂ∞ − K`, with no pole at `∞`, and which is within `ε` of `f` at every point of `K`. -/
theorem weakRunge' {K G : Set ℂ} (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f G) (ε : ℝ) (ε0 : 0 < ε) :
    ∃ R ∈ RatAlg Kᶜ K, Within K ε (fun z : ↥K ↦ f z) R :=
  weakRunge hK hG hKG f hf ε ε0

end

end Conway

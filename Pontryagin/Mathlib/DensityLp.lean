/-
Copyright (c) 2026 The pontryagin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The pontryagin contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.UrysohnsLemma

/-!
# Density of `C_c` in `Lᵖ` on locally compact Hausdorff spaces

This file fills a gap in Mathlib (general-purpose material with no project-specific content)
and is a candidate for upstreaming; see `UPSTREAMING.md` for the audit and target locations.

Let `X` be a locally compact Hausdorff space equipped with a regular Borel measure `μ`.
This file proves that continuous compactly supported functions are dense in `Lᵖ(μ)` for
every exponent `p ≠ ∞`, generalizing the `p = 1` results of `Pontryagin.Mathlib.Density`.

Mathlib's `MeasureTheory/Function/ContinuousMapDense.lean` proves the same statements
under a `[NormalSpace α]` hypothesis, which fails for general locally compact Hausdorff
spaces; here the normal-space Urysohn lemma is replaced by the locally compact one
(`exists_continuous_one_zero_of_isCompact`), exactly as in `Pontryagin.Mathlib.Density`.  The names
carry a prime to avoid clashing with the Mathlib versions.

## Main results

* `exists_continuous_eLpNorm_indicator_sub_le'`: the scaled indicator of a measurable set
  of finite measure can be approximated in the `Lᵖ` seminorm by continuous compactly
  supported functions, for any `p ≠ ∞`.
* `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le'`: **density of `C_c` in
  `Lᵖ`** at the level of functions: any `MemLp` function is within `ε` (in the `eLpNorm`)
  of a continuous compactly supported function.
* `dense_ccLp`: the set of classes in `Lp ℂ p μ` admitting a continuous compactly
  supported representative is dense (for `1 ≤ p`, `p ≠ ∞`); the special case `p = 2`
  (`dense_ccL2`) is what the Plancherel layer consumes.

The proofs mirror `Pontryagin.Mathlib.Density` step by step: the only `p`-specific ingredients,
`MeasureTheory.exists_Lp_half` and `MeasureTheory.exists_eLpNorm_indicator_le`, are already
available in Mathlib for arbitrary `p ≠ ∞`.
-/

noncomputable section

open MeasureTheory Filter Set Function Topology
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [μ.Regular]

/-- On a locally compact Hausdorff space with a regular measure, the (scaled) indicator
function of a measurable set of finite measure can be approximated in the `Lᵖ` seminorm,
`p ≠ ∞`, by continuous compactly supported functions.  Generalization of
`exists_continuous_eLpNorm_indicator_sub_le` (the `p = 1` case in `Pontryagin.Mathlib.Density`);
variant of `MeasureTheory.exists_continuous_eLpNorm_sub_le_of_closed` without the
`NormalSpace` hypothesis. -/
theorem exists_continuous_eLpNorm_indicator_sub_le' (p : ℝ≥0∞) (hp : p ≠ ∞) (c : ℂ)
    {s : Set X} (hs : MeasurableSet s) (hsμ : μ s < ∞) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ g : X → ℂ, eLpNorm (g - s.indicator fun _ => c) p μ ≤ δ ∧
      Continuous g ∧ HasCompactSupport g := by
  obtain ⟨δ₂, δ₂pos, hδ₂⟩ := exists_Lp_half ℂ μ p hδ
  obtain ⟨η, ηpos, hη⟩ := exists_eLpNorm_indicator_le hp c δ₂pos.ne'
  have hη' : (η : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 ηpos.ne'
  -- a compact set `k ⊆ s` catching all of `s` but a set of measure `< η`
  obtain ⟨k, hks, hk_comp, hμsk⟩ := hs.exists_isCompact_sdiff_lt hsμ.ne hη'
  have hk_meas : MeasurableSet k := hk_comp.isClosed.measurableSet
  -- an open set `U ⊇ k` exceeding `k` by a set of measure `< η`
  obtain ⟨U, hkU, hU_open, -, hμUk⟩ :=
    hk_meas.exists_isOpen_sdiff_lt ((measure_mono hks).trans_lt hsμ).ne hη'
  -- Urysohn for locally compact spaces: `f = 1` on `k`, `f = 0` outside `U`
  obtain ⟨f, hf1, hf0, hf_supp, hf_icc⟩ :=
    exists_continuous_one_zero_of_isCompact hk_comp hU_open.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hkU)
  have hg_cont : Continuous fun x => f x • c := (map_continuous f).smul continuous_const
  have hg_supp : HasCompactSupport fun x => f x • c := by
    refine hf_supp.mono fun x hx => ?_
    simp only [Function.mem_support] at hx ⊢
    intro hfx
    exact hx (by rw [hfx, zero_smul])
  refine ⟨fun x => f x • c, ?_, hg_cont, hg_supp⟩
  -- the error is supported in `(U \ k) ∪ (s \ k)`, both of measure `< η`
  have hA : eLpNorm ((fun x => f x • c) - k.indicator fun _ => c) p μ
      ≤ eLpNorm ((U \ k).indicator fun _ => c) p μ := by
    refine eLpNorm_mono fun x => ?_
    simp only [Pi.sub_apply]
    by_cases hxk : x ∈ k
    · simp [Set.indicator_of_mem hxk, hf1 hxk, norm_nonneg]
    · by_cases hxU : x ∈ U
      · simp only [Set.indicator_of_notMem hxk, sub_zero,
          Set.indicator_of_mem (show x ∈ U \ k from ⟨hxU, hxk⟩), norm_smul]
        refine mul_le_of_le_one_left (norm_nonneg c) ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (hf_icc x).1]
        exact (hf_icc x).2
      · have hfx : f x = 0 := hf0 hxU
        simp [Set.indicator_of_notMem hxk,
          Set.indicator_of_notMem (fun h : x ∈ U \ k => hxU h.1), hfx]
  have hB : eLpNorm ((k.indicator fun _ => c) - s.indicator fun _ => c) p μ
      ≤ eLpNorm ((s \ k).indicator fun _ => c) p μ := by
    refine eLpNorm_mono fun x => ?_
    simp only [Pi.sub_apply]
    by_cases hxk : x ∈ k
    · simp [Set.indicator_of_mem hxk, Set.indicator_of_mem (hks hxk), norm_nonneg]
    · by_cases hxs : x ∈ s
      · simp only [Set.indicator_of_notMem hxk, Set.indicator_of_mem hxs,
          Set.indicator_of_mem (show x ∈ s \ k from ⟨hxs, hxk⟩), zero_sub, norm_neg]
        exact le_rfl
      · simp [Set.indicator_of_notMem hxk, Set.indicator_of_notMem hxs,
          Set.indicator_of_notMem (fun h : x ∈ s \ k => hxs h.1)]
  have hA_meas : AEStronglyMeasurable ((fun x => f x • c) - k.indicator fun _ => c) μ :=
    hg_cont.aestronglyMeasurable.sub (aestronglyMeasurable_const.indicator hk_meas)
  have hB_meas : AEStronglyMeasurable
      ((k.indicator fun _ => c) - s.indicator fun _ => c) μ :=
    (aestronglyMeasurable_const.indicator hk_meas).sub
      (aestronglyMeasurable_const.indicator hs)
  have hcomb := hδ₂ _ _ hA_meas hB_meas (hA.trans (hη _ hμUk.le)) (hB.trans (hη _ hμsk.le))
  rw [sub_add_sub_cancel] at hcomb
  exact hcomb.le

/-- **Density of `C_c` in `Lᵖ`, `p ≠ ∞`,** on a locally compact Hausdorff space with a
regular measure: a `MemLp` function can be approximated in the `Lᵖ` seminorm by continuous
compactly supported functions.  Variant of
`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` without the `NormalSpace`
assumption (whence the prime). -/
theorem MemLp.exists_hasCompactSupport_eLpNorm_sub_le' {p : ℝ≥0∞}
    (hp : p ≠ ∞) {f : X → ℂ} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → ℂ, Continuous g ∧ HasCompactSupport g ∧ MemLp g p μ ∧
      eLpNorm (f - g) p μ ≤ ε := by
  have h0P : ∀ (c : ℂ) (s : Set X), MeasurableSet s → μ s < ∞ → ∀ (δ : ℝ≥0∞), δ ≠ 0 →
      ∃ g : X → ℂ, eLpNorm (g - s.indicator fun _ => c) p μ ≤ δ ∧
        Continuous g ∧ HasCompactSupport g :=
    fun c s hs hsμ δ hδ => exists_continuous_eLpNorm_indicator_sub_le' p hp c hs hsμ hδ
  have h1P : ∀ f g : X → ℂ, Continuous f ∧ HasCompactSupport f →
      Continuous g ∧ HasCompactSupport g →
      Continuous (f + g) ∧ HasCompactSupport (f + g) :=
    fun f g hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  have h2P : ∀ f : X → ℂ, Continuous f ∧ HasCompactSupport f →
      AEStronglyMeasurable f μ := fun f hf => hf.1.aestronglyMeasurable
  obtain ⟨g, hg_norm, hg_cont, hg_supp⟩ :=
    hf.induction_dense hp (fun g => Continuous g ∧ HasCompactSupport g) h0P h1P h2P hε
  exact ⟨g, hg_cont, hg_supp, hg_cont.memLp_of_hasCompactSupport hg_supp, hg_norm⟩

/-- **Density of the `C_c` classes in `Lp ℂ p μ`** for `1 ≤ p`, `p ≠ ∞`: the set of `Lᵖ`
classes possessing a continuous compactly supported representative is dense.  This is the
`Lᵖ` analogue of `dense_ccSubmodule` (`Pontryagin.L1Algebra`), packaged at the set level
for the Plancherel layer. -/
theorem dense_ccLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {F : Lp ℂ p μ |
      ∃ f : X → ℂ, Continuous f ∧ HasCompactSupport f ∧ ⇑F =ᵐ[μ] f} := by
  rw [Metric.dense_iff]
  intro F r hr
  have hr2 : ENNReal.ofReal (r / 2) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (half_pos hr)).ne'
  obtain ⟨g, hgc, hgs, hgLp, hg⟩ :=
    (Lp.memLp F).exists_hasCompactSupport_eLpNorm_sub_le' hp hr2
  refine ⟨hgLp.toLp g, Metric.mem_ball.mpr ?_, g, hgc, hgs, hgLp.coeFn_toLp⟩
  have hae : ⇑(hgLp.toLp g - F) =ᵐ[μ] g - ⇑F := by
    filter_upwards [Lp.coeFn_sub (hgLp.toLp g) F, hgLp.coeFn_toLp] with x hx1 hx2
    rw [hx1, Pi.sub_apply, hx2, Pi.sub_apply]
  calc dist (hgLp.toLp g) F
      = (eLpNorm (⇑(hgLp.toLp g - F)) p μ).toReal := by
        rw [dist_eq_norm, Lp.norm_def]
    _ = (eLpNorm (⇑F - g) p μ).toReal := by
        rw [eLpNorm_congr_ae hae, eLpNorm_sub_comm]
    _ ≤ (ENNReal.ofReal (r / 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
    _ = r / 2 := ENNReal.toReal_ofReal (half_pos hr).le
    _ < r := half_lt_self hr

/-- **Density of the `C_c` classes in `L²`**, the special case of `dense_ccLp` consumed by
the Plancherel layer. -/
theorem dense_ccL2 :
    Dense {F : Lp ℂ 2 μ |
      ∃ f : X → ℂ, Continuous f ∧ HasCompactSupport f ∧ ⇑F =ᵐ[μ] f} :=
  dense_ccLp 2 ENNReal.ofNat_ne_top

end MeasureTheory

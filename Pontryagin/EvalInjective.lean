/-
Copyright (c) 2026 The pontryagin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The pontryagin contributors
-/
import Pontryagin.Basic
import Pontryagin.Inversion

/-!
# Injectivity and the inducing property of the double-dual evaluation

For a locally compact Hausdorff abelian group `G`, this file proves two of the three core
facts of Pontryagin duality about the evaluation map
`eval : G → PontryaginDual (PontryaginDual G)`:

* `PontryaginDual.eval_injective_aux`: **characters separate points** — `eval` is injective;
* `PontryaginDual.isInducing_eval_aux`: `eval` is inducing — the topology of `G` is recovered
  from uniform convergence of characters on compact sets of the dual.

Both statements carry no measure-theoretic hypotheses; a regular Haar measure is introduced
inside the proofs (Borel σ-algebras via `borel`, a positive compact set via
`TopologicalSpace.PositiveCompacts`, and `MeasureTheory.Measure.haarMeasure`).

## Proof sketch

*Injectivity.*  Since `eval` is a monoid homomorphism it suffices to show its kernel is
trivial.  If `χ z = 1` for every character `χ` but `z ≠ 1`, pick (via
`exists_positiveType_cc_eq_one`) a continuous compactly supported function `f` of positive
type with `tsupport f ⊆ {z}ᶜ` and `f 1 = 1`.  Fourier inversion represents `f` as an integral
of characters against `𝓕f ⬝ dualHaar μ`; since every character takes the value `1` at `z`,
this forces `f z = f 1 = 1 ≠ 0`, contradicting `z ∉ tsupport f`.

*Inducing.*  By `IsTopologicalGroup.isInducing_iff_nhds_one` it suffices to compare the
neighborhood filters of `1`.  One inequality is the continuity of `eval`.  For the other, fix
`U ∈ 𝓝 (1 : G)` and take `f` of positive type with `tsupport f ⊆ U`, `f 1 = 1`.  The
transform `𝓕f` is nonnegative with total `dualHaar`-integral `1`, and all but `1/4` of this
mass lives on a compact set `Q` of characters
(`exists_isCompact_setIntegral_re_fourierTransform_compl_le`).  If `eval x` lies in the basic
neighborhood `{ω | ∀ χ ∈ Q, ω χ ∈ Circle.centeredArc (1/4)}` of `1` in the double dual
(`PontryaginDual.hasBasis_nhds_one`), then by Fourier inversion
`‖f x - 1‖ ≤ (1/4) ⬝ 1 + 2 ⬝ (1/4) = 3/4`, so `f x ≠ 0` and `x ∈ tsupport f ⊆ U`.
-/

noncomputable section

open Filter Function MeasureTheory Real Set Topology

-- The helper section deliberately uses one coarse hypothesis block (locally compact Hausdorff
-- abelian group with regular Haar measure) rather than minimal per-lemma assumptions.
set_option linter.unusedSectionVars false

-- `show` is used to beta-reduce integrands produced by `integral_congr_ae`.
set_option linter.style.show false

namespace PontryaginDual

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G]

/-! ### Measure-theoretic helpers -/

section HaarHelpers

variable {G}
variable [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

include μ in
/-- If every character of `G` takes the value `1` at `z`, then `z = 1`: otherwise a
positive-type `C_c` function supported in `{z}ᶜ` with `f 1 = 1` would satisfy `f z = f 1 = 1`
by Fourier inversion, contradicting the support constraint. -/
private theorem eq_one_of_forall_char_eq_one {z : G}
    (hχz : ∀ χ : PontryaginDual G, χ z = 1) : z = 1 := by
  by_contra hz1
  have hU : ({z}ᶜ : Set G) ∈ nhds (1 : G) := compl_singleton_mem_nhds (Ne.symm hz1)
  obtain ⟨f, hpt, hfc, hfs, hfsupp, hf1⟩ := exists_positiveType_cc_eq_one μ {z}ᶜ hU
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  -- Fourier inversion turns the kernel condition into translation invariance at `z`
  have hfz : f z = 1 := by
    calc f z
        = ∫ χ, ((χ z : Circle) : ℂ) * fourierTransform μ f χ ∂(dualHaar μ) :=
          hpt.fourier_inversion μ hfc hfi z
      _ = ∫ χ, fourierTransform μ f χ ∂(dualHaar μ) := by
          refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
          show ((χ z : Circle) : ℂ) * fourierTransform μ f χ = fourierTransform μ f χ
          rw [hχz χ, Circle.coe_one, one_mul]
      _ = f 1 := (hpt.fourier_inversion_one μ hfc hfi).symm
      _ = 1 := hf1
  have hz_mem : z ∈ tsupport f :=
    subset_closure (mem_support.mpr (by rw [hfz]; exact one_ne_zero))
  exact hfsupp hz_mem rfl

include μ in
/-- The substantive half of the inducing property: every neighborhood of `1` in `G` contains
the `eval`-preimage of a neighborhood of `1` in the double dual. -/
private theorem exists_nhds_one_preimage_eval_subset {U : Set G} (hU : U ∈ nhds (1 : G)) :
    ∃ V ∈ nhds (1 : PontryaginDual (PontryaginDual G)),
      (eval : G → PontryaginDual (PontryaginDual G)) ⁻¹' V ⊆ U := by
  obtain ⟨f, hpt, hfc, hfs, hfsupp, hf1⟩ := exists_positiveType_cc_eq_one μ U hU
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  obtain ⟨σf, hfin, hreg, hrep⟩ := hpt.exists_bochner_measure μ hfc
  haveI := hfin
  haveI := hreg
  -- the Bochner measure of `f` has total mass `f 1 = 1`
  have hmass : σf.real Set.univ = 1 := by
    have h := hrep 1
    rw [hf1] at h
    have h2 : (fun χ : PontryaginDual G => ((χ (1 : G) : Circle) : ℂ)) = fun _ => (1 : ℂ) :=
      funext fun χ => by simp
    rw [h2, integral_const, Complex.real_smul, mul_one] at h
    exact_mod_cast h.symm
  have hFre_int : Integrable (fun χ => (fourierTransform μ f χ).re) (dualHaar μ) :=
    integrable_re_fourierTransform_dualHaar μ σf hfi hrep
  have hF0 : ∀ χ, 0 ≤ (fourierTransform μ f χ).re :=
    fourierTransform_re_nonneg μ σf hfi hrep
  have hFmass : ∫ χ, (fourierTransform μ f χ).re ∂(dualHaar μ) = 1 := by
    rw [integral_re_fourierTransform_dualHaar μ σf hfi hrep, hmass]
  -- all but `1/4` of the mass of `𝓕f` lives on a compact set `Q` of characters
  obtain ⟨Q, hQ, hQtail⟩ := exists_isCompact_setIntegral_re_fourierTransform_compl_le μ σf
    hfi hrep (ε := 1 / 4) (by norm_num)
  have hπ : (1 : ℝ) / 4 ≤ π := by linarith [Real.two_le_pi]
  -- the polar-type basic neighborhood of `1` in the double dual attached to `(Q, 1/4)`
  refine ⟨{ω : PontryaginDual (PontryaginDual G) | ∀ χ ∈ Q, ω χ ∈ Circle.centeredArc (1 / 4)},
    (hasBasis_nhds_one (G := PontryaginDual G)).mem_of_mem
      (i := (Q, 1 / 4)) ⟨hQ, by norm_num, hπ⟩, fun x hx => ?_⟩
  -- characters in `Q` are uniformly close to `1` at `x`
  have hxQ : ∀ χ ∈ Q, ‖((χ x : Circle) : ℂ) - 1‖ ≤ 1 / 4 := by
    intro χ hχ
    have harc : χ x ∈ Circle.centeredArc (1 / 4) := hx χ hχ
    exact (Circle.norm_coe_sub_one_le_abs_arg (χ x)).trans
      ((Circle.mem_centeredArc hπ).mp harc).le
  -- integrability of the integrands appearing in the estimate
  have hgb : ∀ χ : PontryaginDual G, ‖((χ x : Circle) : ℂ) - 1‖ ≤ 2 := fun χ => by
    calc ‖((χ x : Circle) : ℂ) - 1‖
        ≤ ‖((χ x : Circle) : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Circle.norm_coe, norm_one]; norm_num
  have hgm : AEStronglyMeasurable
      (fun χ : PontryaginDual G => ‖((χ x : Circle) : ℂ) - 1‖) (dualHaar μ) :=
    (((continuous_char_apply x).sub continuous_const).norm).aestronglyMeasurable
  have hgint : Integrable
      (fun χ => ‖((χ x : Circle) : ℂ) - 1‖ * (fourierTransform μ f χ).re) (dualHaar μ) :=
    hFre_int.bdd_mul hgm (Eventually.of_forall fun χ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hgb χ)
  have hFint : Integrable (fourierTransform μ f) (dualHaar μ) :=
    integrable_fourierTransform_dualHaar μ σf hfi hrep
  have hchar_int : Integrable
      (fun χ => ((χ x : Circle) : ℂ) * fourierTransform μ f χ) (dualHaar μ) :=
    hFint.bdd_mul (continuous_char_apply x).aestronglyMeasurable
      (Eventually.of_forall fun χ => le_of_eq (Circle.norm_coe _))
  -- `f x - 1` as an integral against the transform, via Fourier inversion
  have hsub : ∫ χ, (((χ x : Circle) : ℂ) - 1) * fourierTransform μ f χ ∂(dualHaar μ)
      = f x - 1 := by
    have h3 : ∫ χ, (((χ x : Circle) : ℂ) - 1) * fourierTransform μ f χ ∂(dualHaar μ)
        = (∫ χ, ((χ x : Circle) : ℂ) * fourierTransform μ f χ ∂(dualHaar μ))
          - ∫ χ, fourierTransform μ f χ ∂(dualHaar μ) := by
      rw [← integral_sub hchar_int hFint]
      refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
      show (((χ x : Circle) : ℂ) - 1) * fourierTransform μ f χ
        = ((χ x : Circle) : ℂ) * fourierTransform μ f χ - fourierTransform μ f χ
      ring
    rw [h3, ← hpt.fourier_inversion μ hfc hfi x, ← hpt.fourier_inversion_one μ hfc hfi, hf1]
  -- the norm estimate `‖f x - 1‖ ≤ ∫ ‖χ x - 1‖ ⬝ (𝓕f).re`
  have hnorm : ‖f x - 1‖
      ≤ ∫ χ, ‖((χ x : Circle) : ℂ) - 1‖ * (fourierTransform μ f χ).re ∂(dualHaar μ) := by
    rw [← hsub]
    refine norm_integral_le_of_norm_le hgint (Eventually.of_forall fun χ => ?_)
    have hpt_eq : ‖(((χ x : Circle) : ℂ) - 1) * fourierTransform μ f χ‖
        = ‖((χ x : Circle) : ℂ) - 1‖ * (fourierTransform μ f χ).re := by
      rw [norm_mul, fourierTransform_eq_ofReal_re μ σf hrep χ, Complex.ofReal_re,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF0 χ)]
    exact hpt_eq.le
  -- split the estimate over `Q` and `Qᶜ`
  have hsplit : (∫ χ in Q,
        ‖((χ x : Circle) : ℂ) - 1‖ * (fourierTransform μ f χ).re ∂(dualHaar μ))
      + ∫ χ in Qᶜ, ‖((χ x : Circle) : ℂ) - 1‖ * (fourierTransform μ f χ).re ∂(dualHaar μ)
      = ∫ χ, ‖((χ x : Circle) : ℂ) - 1‖ * (fourierTransform μ f χ).re ∂(dualHaar μ) :=
    integral_add_compl hQ.measurableSet hgint
  have hQpart : ∫ χ in Q,
      ‖((χ x : Circle) : ℂ) - 1‖ * (fourierTransform μ f χ).re ∂(dualHaar μ) ≤ 1 / 4 := by
    calc ∫ χ in Q, ‖((χ x : Circle) : ℂ) - 1‖ * (fourierTransform μ f χ).re ∂(dualHaar μ)
        ≤ ∫ χ in Q, 1 / 4 * (fourierTransform μ f χ).re ∂(dualHaar μ) := by
          refine setIntegral_mono_on hgint.integrableOn
            ((hFre_int.const_mul (1 / 4)).integrableOn) hQ.measurableSet fun χ hχ => ?_
          exact mul_le_mul_of_nonneg_right (hxQ χ hχ) (hF0 χ)
      _ = 1 / 4 * ∫ χ in Q, (fourierTransform μ f χ).re ∂(dualHaar μ) :=
          integral_const_mul _ _
      _ ≤ 1 / 4 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [← hFmass]
          exact setIntegral_le_integral hFre_int (Eventually.of_forall hF0)
      _ = 1 / 4 := by norm_num
  have hQcpart : ∫ χ in Qᶜ,
      ‖((χ x : Circle) : ℂ) - 1‖ * (fourierTransform μ f χ).re ∂(dualHaar μ) ≤ 1 / 2 := by
    calc ∫ χ in Qᶜ, ‖((χ x : Circle) : ℂ) - 1‖ * (fourierTransform μ f χ).re ∂(dualHaar μ)
        ≤ ∫ χ in Qᶜ, 2 * (fourierTransform μ f χ).re ∂(dualHaar μ) := by
          refine setIntegral_mono_on hgint.integrableOn
            ((hFre_int.const_mul 2).integrableOn) hQ.measurableSet.compl fun χ _ => ?_
          exact mul_le_mul_of_nonneg_right (hgb χ) (hF0 χ)
      _ = 2 * ∫ χ in Qᶜ, (fourierTransform μ f χ).re ∂(dualHaar μ) := integral_const_mul _ _
      _ ≤ 2 * (1 / 4) := mul_le_mul_of_nonneg_left hQtail (by norm_num)
      _ = 1 / 2 := by norm_num
  -- conclude: `‖f x - 1‖ ≤ 3/4 < 1`, hence `f x ≠ 0` and `x ∈ tsupport f ⊆ U`
  have hfx1 : ‖f x - 1‖ ≤ 3 / 4 := by linarith
  have hfx : f x ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg, norm_one] at hfx1
    norm_num at hfx1
  exact hfsupp (subset_closure (mem_support.mpr hfx))

end HaarHelpers

/-! ### The two duality theorems -/

/-- **Characters separate points**: the evaluation map into the double dual is injective. -/
theorem eval_injective_aux :
    Injective (eval : G → PontryaginDual (PontryaginDual G)) := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  letI : MeasurableSpace (PontryaginDual G) := borel (PontryaginDual G)
  haveI : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  refine (injective_iff_map_eq_one (eval (A := G))).mpr fun z hz => ?_
  refine eq_one_of_forall_char_eq_one (Measure.haarMeasure K₀) fun χ => ?_
  have h := DFunLike.congr_fun hz χ
  simpa using h

/-- The evaluation map is inducing: the topology of `G` is recovered from uniform
convergence of characters on compact sets of the dual. -/
theorem isInducing_eval_aux :
    IsInducing (eval : G → PontryaginDual (PontryaginDual G)) := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  letI : MeasurableSpace (PontryaginDual G) := borel (PontryaginDual G)
  haveI : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  refine IsTopologicalGroup.isInducing_iff_nhds_one.mpr (le_antisymm ?_ ?_)
  · -- continuity of `eval` gives `𝓝 1 ≤ comap eval (𝓝 1)`
    have h : Tendsto (eval : G → PontryaginDual (PontryaginDual G)) (nhds 1)
        (nhds (eval (1 : G))) := (eval (A := G)).continuous.tendsto 1
    have h1 : eval (1 : G) = (1 : PontryaginDual (PontryaginDual G)) := _root_.map_one _
    rw [h1] at h
    exact Filter.tendsto_iff_comap.mp h
  · -- the substance: `comap eval (𝓝 1) ≤ 𝓝 1`
    rw [Filter.le_def]
    intro U hU
    obtain ⟨V, hV, hVsub⟩ :=
      exists_nhds_one_preimage_eval_subset (Measure.haarMeasure K₀) hU
    exact Filter.mem_comap.mpr ⟨V, hV, hVsub⟩

/-! ### Statement fidelity check

The two theorems above literally close the corresponding sorried statements in
`Pontryagin/Duality.lean`. -/

section StatementFidelity

variable (G' : Type*) [CommGroup G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  [LocallyCompactSpace G'] [T2Space G']

example : Injective (eval : G' → PontryaginDual (PontryaginDual G')) :=
  eval_injective_aux G'

example : IsInducing (eval : G' → PontryaginDual (PontryaginDual G')) :=
  isInducing_eval_aux G'

end StatementFidelity

end PontryaginDual

/-
Copyright (c) 2026 The pontryagin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The pontryagin contributors
-/
import Pontryagin.Bochner

/-!
# The dual Haar measure and Fourier inversion for positive-type functions

For a locally compact Hausdorff abelian group `G` with regular Haar measure `μ`, this file
constructs a **Haar measure on the Pontryagin dual** `Ĝ = PontryaginDual G` and proves the
**Fourier inversion formula** for continuous integrable functions of positive type.

Everything is phrased with positive measures only: complex measures are never used; the
blueprint's "inverse Fourier transforms of measures" are systematically replaced by integrals
of bounded continuous densities against finite positive (Bochner) measures.

## Overview of the construction

* For a normalized bump `h` on `G`, the convolution square `e = hℂ ⋆ (hℂ)^*` is a continuous
  compactly supported function of positive type whose Fourier transform is
  `‖𝓕hℂ‖² ≥ 0` (`fourierTransform_mconv_mstar`); by
  `exists_nhds_forall_bump_fourierTransform_close`, for every compact `K ⊆ Ĝ` the bump can be
  chosen so that `𝓕e ≥ 1/4` on `K`.  The bundle (square, Bochner measure, lower bound) is the
  structure `AdmissibleSquare μ K`, produced by `exists_admissibleSquare`.
* `integral_char_mul_fourierTransform` (the *inverse-transform bridge*): for a finite inner
  regular `σ` on `Ĝ` and integrable `f`,
  `∫ χ, χ(x) ⬝ 𝓕f(χ) ∂σ = (f ⋆ φ_σ) x` where `φ_σ(y) = ∫ χ, χ(y) ∂σ`.
* `integral_c0_mul_eq_of_forall_integral_char_mul_eq` (*density-form uniqueness*) and
  `integral_c0_mul_fourierTransform_symm` (*symmetric identity*):
  `∫ a ⬝ 𝓕f ∂σₑ = ∫ a ⬝ 𝓕e ∂σ_f` for all `a ∈ C₀(Ĝ, ℂ)`.
* The **dual Haar functional** `dualLambda μ : C_c(Ĝ, ℝ) →ₚ[ℝ] ℝ`,
  `Λ γ = ∫ χ, γ(χ) / (𝓕e χ).re ∂σₑ` for any admissible square `e` for `tsupport γ`
  (well-defined by `AdmissibleSquare.pairing_congr`), and the **dual Haar measure**
  `dualHaar μ` obtained from it by Riesz–Markov–Kakutani.  It is regular, translation
  invariant (via the modulation action on admissible squares, `AdmissibleSquare.mulChar`),
  nonzero and hence a Haar measure: instances `(dualHaar μ).Regular` and
  `(dualHaar μ).IsHaarMeasure`.
* The **density identity** `integral_cc_mul_fourierTransform_dualHaar`:
  `∫ a ⬝ 𝓕f ∂(dualHaar μ) = ∫ a ∂σ_f` for `a ∈ C_c(Ĝ, ℂ)` and `f` continuous integrable with
  Bochner measure `σ_f`; extended to bounded continuous integrands in
  `integral_bddContinuous_mul_fourierTransform_dualHaar`.
* Consequences: `𝓕f` is real and nonnegative (`IsPositiveType.fourierTransform_im`,
  `fourierTransform_re_nonneg`), integrable against `dualHaar μ`
  (`integrable_fourierTransform_dualHaar`) with total integral the mass of `σ_f`
  (`integral_fourierTransform_dualHaar`), and finally

## Main results

* `IsPositiveType.fourier_inversion` : **Fourier inversion**: for `f` continuous integrable
  of positive type, `f x = ∫ χ, χ(x) ⬝ 𝓕f(χ) ∂(dualHaar μ)`;
* `dualHaar μ` with instances `Regular`, `IsHaarMeasure`;
* `exists_positiveType_cc_eq_one`: normalized positive-type `C_c` functions supported near
  `1`, for the duality layer.
-/

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ComplexConjugate ComplexOrder ENNReal NNReal ZeroAtInfty CompactlySupported
  Pointwise

-- The sections below deliberately use one coarse hypothesis block (locally compact Hausdorff
-- abelian group with regular Haar measure) rather than minimal per-lemma assumptions.
set_option linter.unusedSectionVars false

-- `show` is used pervasively to beta-reduce integrands and to unfold definitional equalities.
set_option linter.style.show false

/-! ### Quotients by a function without zeros on the support of the numerator -/

section QuotientContinuity

variable {X : Type*} [TopologicalSpace X] {𝕜 : Type*} [NormedField 𝕜]

/-- The support of a pointwise quotient is contained in the support of the numerator. -/
theorem support_div_subset (γ u : X → 𝕜) :
    (support fun x => γ x / u x) ⊆ support γ := fun x hx => by
  simp only [mem_support] at hx ⊢
  intro h0
  exact hx (by rw [h0, zero_div])

/-- If `u` has no zeros on `tsupport γ`, the (junk-value) quotient `γ / u` is continuous:
away from `tsupport γ` it vanishes identically, and on a neighborhood of `tsupport γ` the
denominator does not vanish. -/
theorem Continuous.div_of_tsupport_ne_zero {γ u : X → 𝕜} (hγ : Continuous γ)
    (hu : Continuous u) (h : ∀ x ∈ tsupport γ, u x ≠ 0) :
    Continuous fun x => γ x / u x := by
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hx : u x₀ = 0
  · have hx₀ : x₀ ∉ tsupport γ := fun hmem => h x₀ hmem hx
    have hev : (fun x => γ x / u x) =ᶠ[nhds x₀] fun _ => (0 : 𝕜) := by
      filter_upwards [(isClosed_tsupport γ).isOpen_compl.mem_nhds hx₀] with x hxmem
      rw [image_eq_zero_of_notMem_tsupport hxmem, zero_div]
    exact ContinuousAt.congr continuousAt_const hev.symm
  · exact hγ.continuousAt.div hu.continuousAt hx

end QuotientContinuity

/-! ### One-sided testing against nonnegative `C_c` functions -/

section Testing

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- **One-sided testing lemma**: on a locally compact Hausdorff space with an open-positive
measure that is finite on compacts, a continuous real function whose integral against every
nonnegative `C_c` test function is nonnegative is itself nonnegative. -/
theorem Continuous.nonneg_of_forall_integral_cc_nonneg {u : X → ℝ} (hu : Continuous u)
    (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (h : ∀ g : X → ℝ, Continuous g → HasCompactSupport g → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, g x * u x ∂ν) :
    ∀ x, 0 ≤ u x := by
  intro x₀
  by_contra hneg
  push Not at hneg
  -- a neighborhood of `x₀` on which `u < u x₀ / 2 < 0`
  have hVnhds : {x : X | u x < u x₀ / 2} ∈ nhds x₀ := by
    have hc : Continuous fun x => u x := hu
    have h0 : Set.Iio (u x₀ / 2) ∈ nhds (u x₀) := Iio_mem_nhds (by linarith)
    exact hc.continuousAt.preimage_mem_nhds h0
  obtain ⟨V, hVsub, hVopen, hVx₀⟩ := mem_nhds_iff.mp hVnhds
  obtain ⟨L, hLcomp, hL1, hLV⟩ :=
    exists_compact_between isCompact_singleton hVopen (singleton_subset_iff.mpr hVx₀)
  obtain ⟨g, hg1, hg0, hgs, hg01⟩ :=
    exists_continuous_one_zero_of_isCompact isCompact_singleton
      isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hL1)
  have hgnonneg : ∀ x, 0 ≤ g x := fun x => (hg01 x).1
  have hgsupp : tsupport ⇑g ⊆ {x : X | u x < u x₀ / 2} := by
    have h1 : support ⇑g ⊆ interior L := fun x hx => by
      by_contra hxL
      exact hx (hg0 hxL)
    exact ((closure_mono h1).trans
      (closure_minimal interior_subset hLcomp.isClosed)).trans (hLV.trans hVsub)
  have hgint : Integrable (⇑g) ν := g.continuous.integrable_of_hasCompactSupport hgs
  have hgpos : 0 < ∫ x, g x ∂ν :=
    integral_pos_of_integrable_nonneg_nonzero (x := x₀) g.continuous hgint
      (fun x => (hg01 x).1) (by rw [hg1 rfl]; exact one_ne_zero)
  -- the tested integral is at most `(u x₀ / 2) ⬝ ∫ g < 0`
  have hint : Integrable (fun x => g x * u x) ν :=
    (g.continuous.mul hu).integrable_of_hasCompactSupport hgs.mul_right
  have hbound : ∫ x, g x * u x ∂ν ≤ ∫ x, g x * (u x₀ / 2) ∂ν := by
    refine integral_mono hint (hgint.mul_const _) fun x => ?_
    by_cases hx : x ∈ tsupport ⇑g
    · exact mul_le_mul_of_nonneg_left (hgsupp hx).le (hgnonneg x)
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hlt : ∫ x, g x * (u x₀ / 2) ∂ν < 0 := by
    rw [integral_mul_const]
    exact mul_neg_of_pos_of_neg hgpos (by linarith)
  have h0 := h ⇑g g.continuous hgs hgnonneg
  linarith

end Testing

/-! ### Character helpers -/

section CharHelpers

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

theorem continuous_char_apply (x : G) :
    Continuous fun χ : PontryaginDual G => ((χ x : Circle) : ℂ) := by
  refine continuous_subtype_val.comp ?_
  change Continuous fun χ : G →ₜ* Circle => χ x
  exact continuous_eval_const x

/-- Conjugating a character value inverts the argument. -/
theorem conj_char_apply (χ : PontryaginDual G) (y : G) :
    conj ((χ y : Circle) : ℂ) = ((χ y⁻¹ : Circle) : ℂ) := by
  rw [map_inv, Circle.coe_inv_eq_conj]

/-- The multiplicativity of characters, in the form used by the Fubini computations. -/
theorem char_mul_conj_char (χ : PontryaginDual G) (x y : G) :
    ((χ x : Circle) : ℂ) * conj ((χ y : Circle) : ℂ) = ((χ (y⁻¹ * x) : Circle) : ℂ) := by
  rw [conj_char_apply, ← Circle.coe_mul, ← map_mul, mul_comm x y⁻¹]

variable {mΓ : MeasurableSpace (PontryaginDual G)} [OpensMeasurableSpace (PontryaginDual G)]

theorem integrable_char (σ : Measure (PontryaginDual G)) [IsFiniteMeasure σ] (x : G) :
    Integrable (fun χ : PontryaginDual G => ((χ x : Circle) : ℂ)) σ :=
  (integrable_const (1 : ℝ)).mono' (continuous_char_apply x).aestronglyMeasurable
    (Eventually.of_forall fun χ => by simp)

theorem norm_integral_char_le (σ : Measure (PontryaginDual G)) [IsFiniteMeasure σ] (x : G) :
    ‖∫ χ : PontryaginDual G, ((χ x : Circle) : ℂ) ∂σ‖ ≤ σ.real Set.univ := by
  calc ‖∫ χ : PontryaginDual G, ((χ x : Circle) : ℂ) ∂σ‖
      ≤ ∫ _χ : PontryaginDual G, (1 : ℝ) ∂σ :=
        norm_integral_le_of_norm_le (integrable_const _)
          (Eventually.of_forall fun χ => by simp)
    _ = σ.real Set.univ := by rw [integral_const, smul_eq_mul, mul_one]

end CharHelpers

/-! ### The inverse-transform bridge -/

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

section Bridge

variable {mΓ : MeasurableSpace (PontryaginDual G)} [BorelSpace (PontryaginDual G)]

/-- Joint continuity of character evaluation, in the form used by the Fubini kernels. -/
private theorem continuous_char_eval :
    Continuous fun p : PontryaginDual G × G => ((p.1 p.2 : Circle) : ℂ) := by
  change Continuous fun p : (G →ₜ* Circle) × G => ((p.1 p.2 : Circle) : ℂ)
  exact continuous_induced_dom.comp continuous_eval

/-- The inverse-transform bridge for continuous compactly supported functions:
`∫ χ, χ(x) ⬝ 𝓕g(χ) ∂σ = (g ⋆ φ_σ)(x)` where `φ_σ(y) = ∫ χ, χ(y) ∂σ`. -/
private theorem integral_char_mul_fourierTransform_cc
    (σ : Measure (PontryaginDual G)) [IsFiniteMeasure σ] [σ.InnerRegularCompactLTTop]
    {g : G → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g) (x : G) :
    ∫ χ, (χ x : ℂ) * fourierTransform μ g χ ∂σ
      = mconv μ g (fun y => ∫ χ, (χ y : ℂ) ∂σ) x := by
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  have hFc : Continuous (uncurry fun (χ : PontryaginDual G) (y : G) =>
      (χ x : ℂ) * (g y * conj (χ y : ℂ))) :=
    (((continuous_char_apply x).comp continuous_fst)).mul
      ((hgc.comp continuous_snd).mul (Complex.continuous_conj.comp continuous_char_eval))
  have hFb : ∀ (χ : PontryaginDual G) (y : G),
      ‖(χ x : ℂ) * (g y * conj (χ y : ℂ))‖ ≤ C := by
    intro χ y
    rw [norm_mul, Circle.norm_coe, one_mul, norm_mul, RCLike.norm_conj, Circle.norm_coe,
      mul_one]
    exact hC y
  have hFsupp : ∀ (χ : PontryaginDual G) (y : G), y ∉ tsupport g →
      (χ x : ℂ) * (g y * conj (χ y : ℂ)) = 0 := fun χ y hy => by
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, mul_zero]
  calc ∫ χ, (χ x : ℂ) * fourierTransform μ g χ ∂σ
      = ∫ χ, ∫ y, (χ x : ℂ) * (g y * conj (χ y : ℂ)) ∂μ ∂σ := by
        refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
        show (χ x : ℂ) * fourierTransform μ g χ = _
        rw [fourierTransform_apply, ← integral_const_mul]
    _ = ∫ y, ∫ χ, (χ x : ℂ) * (g y * conj (χ y : ℂ)) ∂σ ∂μ :=
        integral_integral_swap_of_finite_of_compactSupport hFc hFb hgs hFsupp
    _ = mconv μ g (fun y => ∫ χ, (χ y : ℂ) ∂σ) x := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        show ∫ χ, (χ x : ℂ) * (g y * conj (χ y : ℂ)) ∂σ
          = g y * ∫ χ, (χ (y⁻¹ * x) : ℂ) ∂σ
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
        show (χ x : ℂ) * (g y * conj (χ y : ℂ)) = g y * (χ (y⁻¹ * x) : ℂ)
        rw [← char_mul_conj_char χ x y]
        ring

/-- **The inverse-transform bridge.**  For a finite inner regular measure `σ` on the dual
group and an integrable `f : G → ℂ`,

`∫ χ, χ(x) ⬝ 𝓕f(χ) ∂σ = (f ⋆ φ_σ)(x)`,   where `φ_σ(y) = ∫ χ, χ(y) ∂σ`.

For `f` continuous compactly supported this is a direct Fubini computation; the general case
follows by `L¹`-approximation. -/
theorem integral_char_mul_fourierTransform
    (σ : Measure (PontryaginDual G)) [IsFiniteMeasure σ] [σ.InnerRegularCompactLTTop]
    {f : G → ℂ} (hfi : Integrable f μ) (x : G) :
    ∫ χ, (χ x : ℂ) * fourierTransform μ f χ ∂σ
      = mconv μ f (fun y => ∫ χ, (χ y : ℂ) ∂σ) x := by
  set φσ : G → ℂ := fun y => ∫ χ, (χ y : ℂ) ∂σ with hφσdef
  have hφσc : Continuous φσ := continuous_integral_char σ
  set M : ℝ := σ.real Set.univ with hMdef
  have hM0 : 0 ≤ M := measureReal_nonneg
  have hφσb : ∀ y, ‖φσ y‖ ≤ M := fun y => norm_integral_char_le σ y
  have hshiftm : AEStronglyMeasurable (fun y => φσ (y⁻¹ * x)) μ :=
    (hφσc.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
  have hIchar : ∀ {u : G → ℂ}, Integrable u μ →
      Integrable (fun χ => (χ x : ℂ) * fourierTransform μ u χ) σ := by
    intro u hui
    refine (integrable_const (∫ z, ‖u z‖ ∂μ)).mono'
      (((continuous_char_apply x).mul
        (continuous_fourierTransform μ hui)).aestronglyMeasurable)
      (Eventually.of_forall fun χ => ?_)
    rw [norm_mul, Circle.norm_coe, one_mul]
    exact norm_fourierTransform_le μ u χ
  have key : ∀ δ : ℝ, 0 < δ →
      ‖(∫ χ, (χ x : ℂ) * fourierTransform μ f χ ∂σ) - mconv μ f φσ x‖ ≤ δ * (2 * M) := by
    intro δ hδ
    obtain ⟨v, hvc, hvs, hvi, hvclose⟩ := exists_hasCompactSupport_integral_norm_sub_le hfi hδ
    have hbase := integral_char_mul_fourierTransform_cc μ σ hvc hvs x
    -- the σ-side error
    have h1 : ‖(∫ χ, (χ x : ℂ) * fourierTransform μ f χ ∂σ)
        - ∫ χ, (χ x : ℂ) * fourierTransform μ v χ ∂σ‖ ≤ δ * M := by
      rw [← integral_sub (hIchar hfi) (hIchar hvi)]
      calc ‖∫ χ, ((χ x : ℂ) * fourierTransform μ f χ
              - (χ x : ℂ) * fourierTransform μ v χ) ∂σ‖
          ≤ ∫ _χ, δ ∂σ := by
            refine norm_integral_le_of_norm_le (integrable_const _)
              (Eventually.of_forall fun χ => ?_)
            rw [← mul_sub, norm_mul, Circle.norm_coe, one_mul]
            exact (norm_fourierTransform_sub_le μ hfi hvi χ).trans hvclose
        _ = δ * M := by rw [integral_const, smul_eq_mul, mul_comm]
    -- the convolution-side error
    have hIf : Integrable (fun y => f y * φσ (y⁻¹ * x)) μ :=
      hfi.mul_bdd hshiftm (Eventually.of_forall fun y => hφσb _)
    have hIv : Integrable (fun y => v y * φσ (y⁻¹ * x)) μ :=
      hvi.mul_bdd hshiftm (Eventually.of_forall fun y => hφσb _)
    have h2 : ‖mconv μ v φσ x - mconv μ f φσ x‖ ≤ δ * M := by
      have hsub : mconv μ v φσ x - mconv μ f φσ x
          = ∫ y, (v y - f y) * φσ (y⁻¹ * x) ∂μ := by
        rw [mconv_apply, mconv_apply, ← integral_sub hIv hIf]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        ring
      rw [hsub]
      calc ‖∫ y, (v y - f y) * φσ (y⁻¹ * x) ∂μ‖
          ≤ ∫ y, ‖v y - f y‖ * M ∂μ := by
            refine norm_integral_le_of_norm_le ((hvi.sub hfi).norm.mul_const M)
              (Eventually.of_forall fun y => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hφσb _) (norm_nonneg _)
        _ = (∫ y, ‖v y - f y‖ ∂μ) * M := integral_mul_const _ _
        _ ≤ δ * M := by
            refine mul_le_mul_of_nonneg_right ?_ hM0
            calc ∫ y, ‖v y - f y‖ ∂μ
                = ∫ y, ‖f y - v y‖ ∂μ :=
                  integral_congr_ae (Eventually.of_forall fun y => norm_sub_rev _ _)
              _ ≤ δ := hvclose
    calc ‖(∫ χ, (χ x : ℂ) * fourierTransform μ f χ ∂σ) - mconv μ f φσ x‖
        = ‖((∫ χ, (χ x : ℂ) * fourierTransform μ f χ ∂σ)
              - ∫ χ, (χ x : ℂ) * fourierTransform μ v χ ∂σ)
            + (mconv μ v φσ x - mconv μ f φσ x)‖ := by
          rw [← hbase]
          congr 1
          ring
      _ ≤ ‖(∫ χ, (χ x : ℂ) * fourierTransform μ f χ ∂σ)
              - ∫ χ, (χ x : ℂ) * fourierTransform μ v χ ∂σ‖
            + ‖mconv μ v φσ x - mconv μ f φσ x‖ := norm_add_le _ _
      _ ≤ δ * M + δ * M := add_le_add h1 h2
      _ = δ * (2 * M) := by ring
  have h0 : ‖(∫ χ, (χ x : ℂ) * fourierTransform μ f χ ∂σ) - mconv μ f φσ x‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hδ : 0 < ε / (2 * M + 1) := by positivity
    refine (key _ hδ).trans ?_
    have h3 : ε / (2 * M + 1) * (2 * M) ≤ ε / (2 * M + 1) * (2 * M + 1) := by
      refine mul_le_mul_of_nonneg_left (by linarith) hδ.le
    rw [div_mul_cancel₀ ε (by positivity : (2 * M + 1 : ℝ) ≠ 0)] at h3
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

end Bridge

/-! ### Density-form uniqueness and the symmetric identity -/

section DensityUniqueness

variable {mΓ : MeasurableSpace (PontryaginDual G)} [BorelSpace (PontryaginDual G)]

/-- Integration of `C₀` functions against a bounded continuous density and a finite measure
is a continuous functional on `C₀`. -/
private theorem continuous_integral_c0_mul (σ : Measure (PontryaginDual G))
    [IsFiniteMeasure σ] {u : PontryaginDual G → ℂ} (huc : Continuous u) {C : ℝ}
    (hub : ∀ χ, ‖u χ‖ ≤ C) :
    Continuous fun a : C₀(PontryaginDual G, ℂ) => ∫ χ, a χ * u χ ∂σ := by
  set C' : ℝ := max C 0 with hC'def
  have hub' : ∀ χ, ‖u χ‖ ≤ C' := fun χ => (hub χ).trans (le_max_left _ _)
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hint : ∀ a : C₀(PontryaginDual G, ℂ), Integrable (fun χ => a χ * u χ) σ := fun a =>
    (integrable_const (‖a‖ * C')).mono' ((map_continuous a).mul huc).aestronglyMeasurable
      (Eventually.of_forall fun χ => by
        rw [norm_mul]
        exact mul_le_mul (a.norm_apply_le χ) (hub' χ) (norm_nonneg _) (norm_nonneg a))
  refine (LipschitzWith.of_dist_le_mul
    (K := (C' * σ.real Set.univ).toNNReal) fun a b => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : (∫ χ, a χ * u χ ∂σ) - ∫ χ, b χ * u χ ∂σ = ∫ χ, (a - b) χ * u χ ∂σ := by
    rw [← integral_sub (hint a) (hint b)]
    refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
    show a χ * u χ - b χ * u χ = (a - b) χ * u χ
    rw [ZeroAtInftyContinuousMap.sub_apply]
    ring
  rw [hsub]
  calc ‖∫ χ, (a - b) χ * u χ ∂σ‖
      ≤ ∫ _χ, ‖a - b‖ * C' ∂σ := by
        refine norm_integral_le_of_norm_le (integrable_const _)
          (Eventually.of_forall fun χ => ?_)
        rw [norm_mul]
        exact mul_le_mul ((a - b).norm_apply_le χ) (hub' χ) (norm_nonneg _) (norm_nonneg _)
    _ = C' * σ.real Set.univ * ‖a - b‖ := by
        rw [integral_const, smul_eq_mul]
        ring
    _ ≤ ((C' * σ.real Set.univ).toNNReal : ℝ) * ‖a - b‖ :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _)

/-- Fubini for a `C_c` transform against a bounded continuous density: the inner integral
localizes the hypothesis of `integral_c0_mul_eq_of_forall_integral_char_mul_eq`. -/
private theorem integral_fourier_mul_density (σ : Measure (PontryaginDual G))
    [IsFiniteMeasure σ] [σ.InnerRegularCompactLTTop]
    {u : PontryaginDual G → ℂ} (huc : Continuous u) {C : ℝ} (hub : ∀ χ, ‖u χ‖ ≤ C)
    {g : G → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g) :
    ∫ χ, fourierTransform μ g χ * u χ ∂σ
      = ∫ y, g y * ∫ χ, (χ y⁻¹ : ℂ) * u χ ∂σ ∂μ := by
  obtain ⟨Cg, hCg⟩ := hgc.bounded_above_of_compact_support hgs
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (u 1)) (hub 1)
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg (g 1)) (hCg 1)
  have hFc : Continuous (uncurry fun (χ : PontryaginDual G) (y : G) =>
      g y * conj (χ y : ℂ) * u χ) :=
    ((hgc.comp continuous_snd).mul
      (Complex.continuous_conj.comp continuous_char_eval)).mul (huc.comp continuous_fst)
  have hFb : ∀ (χ : PontryaginDual G) (y : G), ‖g y * conj (χ y : ℂ) * u χ‖ ≤ Cg * C := by
    intro χ y
    rw [norm_mul, norm_mul, RCLike.norm_conj, Circle.norm_coe, mul_one]
    exact mul_le_mul (hCg y) (hub χ) (norm_nonneg _) hCg0
  have hFsupp : ∀ (χ : PontryaginDual G) (y : G), y ∉ tsupport g →
      g y * conj (χ y : ℂ) * u χ = 0 := fun χ y hy => by
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul]
  calc ∫ χ, fourierTransform μ g χ * u χ ∂σ
      = ∫ χ, ∫ y, g y * conj (χ y : ℂ) * u χ ∂μ ∂σ := by
        refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
        show fourierTransform μ g χ * u χ = _
        rw [fourierTransform_apply, ← integral_mul_const]
    _ = ∫ y, ∫ χ, g y * conj (χ y : ℂ) * u χ ∂σ ∂μ :=
        integral_integral_swap_of_finite_of_compactSupport hFc hFb hgs hFsupp
    _ = ∫ y, g y * ∫ χ, (χ y⁻¹ : ℂ) * u χ ∂σ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        show ∫ χ, g y * conj (χ y : ℂ) * u χ ∂σ = g y * ∫ χ, (χ y⁻¹ : ℂ) * u χ ∂σ
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
        show g y * conj (χ y : ℂ) * u χ = g y * ((χ y⁻¹ : ℂ) * u χ)
        rw [← conj_char_apply]
        ring

include μ in
/-- **Density-form uniqueness.**  If two bounded continuous densities against two finite
inner regular measures on the dual have the same "inverse transforms"
`∫ χ, χ(x) ⬝ uᵢ(χ) ∂σᵢ` for every `x : G`, then they integrate all of `C₀(Ĝ, ℂ)` equally. -/
theorem integral_c0_mul_eq_of_forall_integral_char_mul_eq
    {σ₁ σ₂ : Measure (PontryaginDual G)} [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    [σ₁.InnerRegularCompactLTTop] [σ₂.InnerRegularCompactLTTop]
    {u₁ u₂ : PontryaginDual G → ℂ} (hu₁c : Continuous u₁) (hu₂c : Continuous u₂)
    {C₁ C₂ : ℝ} (hu₁b : ∀ χ, ‖u₁ χ‖ ≤ C₁) (hu₂b : ∀ χ, ‖u₂ χ‖ ≤ C₂)
    (h : ∀ x : G, ∫ χ, (χ x : ℂ) * u₁ χ ∂σ₁ = ∫ χ, (χ x : ℂ) * u₂ χ ∂σ₂)
    (a : C₀(PontryaginDual G, ℂ)) :
    ∫ χ, a χ * u₁ χ ∂σ₁ = ∫ χ, a χ * u₂ χ ∂σ₂ := by
  have hEqOn : Set.EqOn (fun a : C₀(PontryaginDual G, ℂ) => ∫ χ, a χ * u₁ χ ∂σ₁)
      (fun a : C₀(PontryaginDual G, ℂ) => ∫ χ, a χ * u₂ χ ∂σ₂)
      (ccFourierSubalgebra μ : Set C₀(PontryaginDual G, ℂ)) := by
    rintro _ ⟨g, hgc, hgs, rfl⟩
    show ∫ χ, fourierTransform μ g χ * u₁ χ ∂σ₁ = ∫ χ, fourierTransform μ g χ * u₂ χ ∂σ₂
    rw [integral_fourier_mul_density μ σ₁ hu₁c hu₁b hgc hgs,
      integral_fourier_mul_density μ σ₂ hu₂c hu₂b hgc hgs]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show g y * ∫ χ, (χ y⁻¹ : ℂ) * u₁ χ ∂σ₁ = g y * ∫ χ, (χ y⁻¹ : ℂ) * u₂ χ ∂σ₂
    rw [h y⁻¹]
  have hfun : (fun a : C₀(PontryaginDual G, ℂ) => ∫ χ, a χ * u₁ χ ∂σ₁)
      = fun a : C₀(PontryaginDual G, ℂ) => ∫ χ, a χ * u₂ χ ∂σ₂ :=
    Continuous.ext_on (dense_ccFourierSubalgebra μ)
      (continuous_integral_c0_mul σ₁ hu₁c hu₁b)
      (continuous_integral_c0_mul σ₂ hu₂c hu₂b) hEqOn
  exact congrFun hfun a

/-- **The symmetric identity.**  For `e` continuous compactly supported with Bochner measure
`σₑ` and `f` integrable with Bochner measure `σ_f`,

`∫ χ, a(χ) ⬝ 𝓕f(χ) ∂σₑ = ∫ χ, a(χ) ⬝ 𝓕e(χ) ∂σ_f`   for every `a ∈ C₀(Ĝ, ℂ)`. -/
theorem integral_c0_mul_fourierTransform_symm
    {e : G → ℂ} (hec : Continuous e) (hes : HasCompactSupport e)
    (σe : Measure (PontryaginDual G)) [IsFiniteMeasure σe] [σe.InnerRegularCompactLTTop]
    (hrepe : ∀ x : G, e x = ∫ χ, (χ x : ℂ) ∂σe)
    {f : G → ℂ} (hfi : Integrable f μ)
    (σf : Measure (PontryaginDual G)) [IsFiniteMeasure σf] [σf.InnerRegularCompactLTTop]
    (hrepf : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf)
    (a : C₀(PontryaginDual G, ℂ)) :
    ∫ χ, a χ * fourierTransform μ f χ ∂σe = ∫ χ, a χ * fourierTransform μ e χ ∂σf := by
  have hei : Integrable e μ := hec.integrable_of_hasCompactSupport hes
  refine integral_c0_mul_eq_of_forall_integral_char_mul_eq μ
    (continuous_fourierTransform μ hfi) (continuous_fourierTransform μ hei)
    (fun χ => norm_fourierTransform_le μ f χ) (fun χ => norm_fourierTransform_le μ e χ)
    (fun x => ?_) a
  rw [integral_char_mul_fourierTransform μ σe hfi x,
    integral_char_mul_fourierTransform μ σf hei x,
    show (fun y => ∫ χ, (χ y : ℂ) ∂σe) = e from funext fun y => (hrepe y).symm,
    show (fun y => ∫ χ, (χ y : ℂ) ∂σf) = f from funext fun y => (hrepf y).symm,
    mconv_comm μ f e]

end DensityUniqueness

/-! ### Transforms of convolution squares -/

section ConvolutionSquare

variable {mΓ : MeasurableSpace (PontryaginDual G)} [BorelSpace (PontryaginDual G)]

/-- The Fourier transform of a convolution square is the (real, nonnegative) squared modulus
of the transform: `𝓕(g ⋆ g^*) = ‖𝓕g‖²`. -/
theorem fourierTransform_mconv_mstar {g : G → ℂ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) (χ : PontryaginDual G) :
    fourierTransform μ (mconv μ g (mstar g)) χ
      = ((‖fourierTransform μ g χ‖ ^ 2 : ℝ) : ℂ) := by
  rw [fourierTransform_mconv μ hgc hgs hgc.mstar hgs.mstar χ, fourierTransform_mstar μ g χ,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

end ConvolutionSquare

/-! ### Admissible squares -/

section AdmissibleSquares

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- An **admissible square for a compact set `K` of characters**: a continuous compactly
supported function `e` on `G` (in practice a convolution square of a bump) whose Fourier
transform is real, nonnegative, and at least `1/4` on `K`, together with its Bochner measure
`σ` (finite, regular, nonzero, representing `e`).  This is the data from which the dual Haar
functional is built. -/
structure AdmissibleSquare (K : Set (PontryaginDual G)) where
  /-- The convolution square on the group. -/
  e : G → ℂ
  cont : Continuous e
  supp : HasCompactSupport e
  transform_im : ∀ χ, (fourierTransform μ e χ).im = 0
  transform_nonneg : ∀ χ, 0 ≤ (fourierTransform μ e χ).re
  lower : ∀ χ ∈ K, (4 : ℝ)⁻¹ ≤ (fourierTransform μ e χ).re
  /-- The Bochner measure of `e`. -/
  σ : Measure (PontryaginDual G)
  finite : IsFiniteMeasure σ
  regular : σ.Regular
  ne_zero : σ ≠ 0
  rep : ∀ x : G, e x = ∫ χ, (χ x : ℂ) ∂σ

namespace AdmissibleSquare

variable {K K' : Set (PontryaginDual G)}

theorem integrable (E : AdmissibleSquare μ K) : Integrable E.e μ :=
  E.cont.integrable_of_hasCompactSupport E.supp

theorem continuous_transform (E : AdmissibleSquare μ K) :
    Continuous (fourierTransform μ E.e) :=
  continuous_fourierTransform μ (E.integrable μ)

/-- The transform of an admissible square is (the coercion of) its real part. -/
theorem transform_eq (E : AdmissibleSquare μ K) (χ : PontryaginDual G) :
    fourierTransform μ E.e χ = (((fourierTransform μ E.e χ).re : ℝ) : ℂ) :=
  Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im, E.transform_im χ])

theorem transform_ne_zero (E : AdmissibleSquare μ K) {χ : PontryaginDual G} (hχ : χ ∈ K) :
    fourierTransform μ E.e χ ≠ 0 := by
  intro h0
  have h := E.lower χ hχ
  rw [h0, Complex.zero_re] at h
  norm_num at h

theorem re_transform_ne_zero (E : AdmissibleSquare μ K) {χ : PontryaginDual G}
    (hχ : χ ∈ K) : (fourierTransform μ E.e χ).re ≠ 0 := by
  have h := E.lower χ hχ
  intro h0
  rw [h0] at h
  norm_num at h

end AdmissibleSquare

/-- **Existence of admissible squares**: for every compact `K ⊆ Ĝ` there is an admissible
square, obtained as the convolution square of a normalized bump supported close enough
to `1` (via `exists_nhds_forall_bump_fourierTransform_close`). -/
theorem exists_admissibleSquare {K : Set (PontryaginDual G)} (hK : IsCompact K) :
    Nonempty (AdmissibleSquare μ K) := by
  obtain ⟨U, hU, hUprop⟩ :=
    exists_nhds_forall_bump_fourierTransform_close μ hK (ε := 2⁻¹) (by norm_num)
  obtain ⟨h, hhc, hhs, hh0, hhsupp, hhint⟩ := exists_normalized_bump μ U hU
  set hC : G → ℂ := fun x => ((h x : ℝ) : ℂ) with hhCdef
  have hhCc : Continuous hC := Complex.continuous_ofReal.comp hhc
  have hhCs : HasCompactSupport hC := hhs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hec : Continuous (mconv μ hC (mstar hC)) := hhCc.mconv μ hhCs hhCc.mstar hhCs.mstar
  have hes : HasCompactSupport (mconv μ hC (mstar hC)) := hhCs.mconv μ hhCs.mstar
  have hpt : IsPositiveType (mconv μ hC (mstar hC)) := isPositiveType_mconv_mstar μ hhCc hhCs
  have htrans : ∀ χ, fourierTransform μ (mconv μ hC (mstar hC)) χ
      = ((‖fourierTransform μ hC χ‖ ^ 2 : ℝ) : ℂ) := fun χ =>
    fourierTransform_mconv_mstar μ hhCc hhCs χ
  obtain ⟨σ, hfin, hreg, hrep⟩ := hpt.exists_bochner_measure μ hec
  haveI := hfin
  -- the lower bound on `K`
  have hlow : ∀ χ ∈ K, (4 : ℝ)⁻¹ ≤ (fourierTransform μ (mconv μ hC (mstar hC)) χ).re := by
    intro χ hχ
    have hclose := hUprop h hhc hhs hh0 hhsupp hhint χ hχ
    have hge : (2 : ℝ)⁻¹ ≤ ‖fourierTransform μ hC χ‖ := by
      have h1 : (1 : ℝ) - ‖fourierTransform μ hC χ‖ ≤ 2⁻¹ := by
        calc (1 : ℝ) - ‖fourierTransform μ hC χ‖
            = ‖(1 : ℂ)‖ - ‖fourierTransform μ hC χ‖ := by rw [norm_one]
          _ ≤ ‖(1 : ℂ) - fourierTransform μ hC χ‖ := norm_sub_norm_le _ _
          _ = ‖fourierTransform μ hC χ - 1‖ := norm_sub_rev _ _
          _ ≤ 2⁻¹ := hclose
      linarith
    rw [htrans χ, Complex.ofReal_re]
    calc (4 : ℝ)⁻¹ = (2 : ℝ)⁻¹ ^ 2 := by norm_num
      _ ≤ ‖fourierTransform μ hC χ‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hge 2
  -- positivity of the mass
  have hr : 0 < ∫ y, ‖hC y‖ ^ 2 ∂μ := by
    have hsqeq : (fun y => ‖hC y‖ ^ 2) = fun y => h y ^ 2 := funext fun y => by
      show ‖((h y : ℝ) : ℂ)‖ ^ 2 = h y ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hsqeq]
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, h x₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [show h = fun _ => (0 : ℝ) from funext hcon] at hhint
      simp at hhint
    have hsqc : Continuous fun y => h y ^ 2 := by fun_prop
    have hsqs : HasCompactSupport fun y => h y ^ 2 := by
      refine hhs.mono fun y hy => ?_
      simp only [mem_support] at hy ⊢
      exact fun h0 => hy (by rw [h0]; ring)
    exact integral_pos_of_integrable_nonneg_nonzero (x := x₀) hsqc
      (hsqc.integrable_of_hasCompactSupport hsqs) (fun y => sq_nonneg _)
      (pow_ne_zero 2 hx₀)
  refine ⟨⟨mconv μ hC (mstar hC), hec, hes,
    (fun χ => by rw [htrans χ]; exact Complex.ofReal_im _),
    (fun χ => by rw [htrans χ, Complex.ofReal_re]; exact sq_nonneg _),
    hlow, σ, hfin, hreg, ?_, hrep⟩⟩
  -- `σ ≠ 0` because the total mass is `e 1 = ∫ ‖hC‖² > 0`
  intro h0
  have hmass := hpt.bochner_measure_mass hrep
  rw [mconv_mstar_self_one μ hC, h0] at hmass
  have : (∫ y, ‖hC y‖ ^ 2 ∂μ) = (0 : Measure (PontryaginDual G)).real Set.univ := by
    exact_mod_cast hmass
  rw [show (0 : Measure (PontryaginDual G)).real Set.univ = 0 by
    simp [measureReal_def]] at this
  exact hr.ne' this

/-! ### Modulation of admissible squares -/

namespace AdmissibleSquare

variable {K : Set (PontryaginDual G)}

/-- **Modulation**: multiplying an admissible square by a character `η` produces an
admissible square for the translated compact set `η ⬝ K`, whose Bochner measure is the
pushforward of the original one under translation by `η`. -/
def mulChar (E : AdmissibleSquare μ K) (η : PontryaginDual G) :
    AdmissibleSquare μ ((η * ·) '' K) where
  e := fun x => E.e x * ((η x : Circle) : ℂ)
  cont := (E.cont).mul (continuous_induced_dom.comp (map_continuous η))
  supp := (E.supp).mono fun x hx => by
    simp only [mem_support] at hx ⊢
    exact fun h0 => hx (by rw [h0, zero_mul])
  transform_im := fun χ => by
    rw [fourierTransform_mul_char μ E.e η χ]
    exact E.transform_im (χ / η)
  transform_nonneg := fun χ => by
    rw [fourierTransform_mul_char μ E.e η χ]
    exact E.transform_nonneg (χ / η)
  lower := by
    rintro _ ⟨ψ, hψ, rfl⟩
    rw [fourierTransform_mul_char μ E.e η (η * ψ), mul_div_cancel_left]
    exact E.lower ψ hψ
  σ := E.σ.map (Homeomorph.mulLeft η).toMeasurableEquiv
  finite := by
    haveI := E.finite
    exact Measure.isFiniteMeasure_map (E.σ) _
  regular := by
    haveI := E.regular
    rw [show (E.σ).map ⇑(Homeomorph.mulLeft η).toMeasurableEquiv
        = (E.σ).map ⇑(Homeomorph.mulLeft η) by
      rw [Homeomorph.toMeasurableEquiv_coe]]
    exact Measure.Regular.map (Homeomorph.mulLeft η)
  ne_zero := by
    intro h0
    refine E.ne_zero (Measure.measure_univ_eq_zero.mp ?_)
    have h1 : ((E.σ).map ⇑(Homeomorph.mulLeft η).toMeasurableEquiv) Set.univ
        = (E.σ) Set.univ := by
      rw [Measure.map_apply (Homeomorph.mulLeft η).toMeasurableEquiv.measurable
        MeasurableSet.univ, Set.preimage_univ]
    rw [h0] at h1
    simpa using h1.symm
  rep := fun x => by
    haveI := E.finite
    have h1 : ∫ χ, (χ x : ℂ) ∂((E.σ).map (Homeomorph.mulLeft η).toMeasurableEquiv)
        = ∫ χ, (((Homeomorph.mulLeft η).toMeasurableEquiv χ) x : ℂ) ∂(E.σ) :=
      MeasureTheory.integral_map_equiv _ _
    have h2 : ∀ χ : PontryaginDual G,
        ((((Homeomorph.mulLeft η).toMeasurableEquiv χ) x : Circle) : ℂ)
          = ((η x : Circle) : ℂ) * ((χ x : Circle) : ℂ) := fun χ => by
      show (((η * χ) x : Circle) : ℂ) = _
      rw [show (η * χ) x = η x * χ x from rfl, Circle.coe_mul]
    rw [h1]
    refine Eq.symm ?_
    calc ∫ χ, (((Homeomorph.mulLeft η).toMeasurableEquiv χ) x : ℂ) ∂(E.σ)
        = ∫ χ, ((η x : Circle) : ℂ) * ((χ x : Circle) : ℂ) ∂(E.σ) :=
          integral_congr_ae (Eventually.of_forall fun χ => h2 χ)
      _ = ((η x : Circle) : ℂ) * ∫ χ, (χ x : ℂ) ∂(E.σ) := integral_const_mul _ _
      _ = E.e x * ((η x : Circle) : ℂ) := by rw [← E.rep x]; ring

theorem mulChar_transform (E : AdmissibleSquare μ K) (η χ : PontryaginDual G) :
    fourierTransform μ (E.mulChar μ η).e χ = fourierTransform μ E.e (χ / η) :=
  fourierTransform_mul_char μ E.e η χ

theorem mulChar_σ (E : AdmissibleSquare μ K) (η : PontryaginDual G) :
    (E.mulChar μ η).σ = (E.σ).map (Homeomorph.mulLeft η).toMeasurableEquiv := rfl

end AdmissibleSquare

/-! ### The pairing against an admissible square -/

namespace AdmissibleSquare

variable {K K' : Set (PontryaginDual G)}

/-- The pairing of a real function on the dual against an admissible square:
`E.pairing γ = ∫ χ, γ(χ) / (𝓕e χ).re ∂σₑ`. -/
def pairing (E : AdmissibleSquare μ K) (γ : PontryaginDual G → ℝ) : ℝ :=
  ∫ χ, γ χ / (fourierTransform μ E.e χ).re ∂(E.σ)

theorem continuous_div_re (E : AdmissibleSquare μ K) {γ : PontryaginDual G → ℝ}
    (hγc : Continuous γ) (hγK : tsupport γ ⊆ K) :
    Continuous fun χ => γ χ / (fourierTransform μ E.e χ).re :=
  hγc.div_of_tsupport_ne_zero (Complex.continuous_re.comp (E.continuous_transform μ))
    fun _χ hχ => E.re_transform_ne_zero μ (hγK hχ)

theorem integrable_div_re (E : AdmissibleSquare μ K) {γ : PontryaginDual G → ℝ}
    (hγc : Continuous γ) (hγs : HasCompactSupport γ) (hγK : tsupport γ ⊆ K) :
    Integrable (fun χ => γ χ / (fourierTransform μ E.e χ).re) (E.σ) := by
  haveI := E.finite
  exact (E.continuous_div_re μ hγc hγK).integrable_of_hasCompactSupport
    (hγs.mono (support_div_subset _ _))

/-- **Well-definedness of the dual Haar pairing**: two admissible squares assign the same
pairing to any `C_c` function supported in both of their compact sets.  This is the heart of
the construction of the dual Haar measure; it follows from the symmetric identity applied to
the compactly supported quotient `γ / (𝓕e ⬝ 𝓕e')`. -/
theorem pairing_congr (E : AdmissibleSquare μ K) (E' : AdmissibleSquare μ K')
    {γ : PontryaginDual G → ℝ} (hγc : Continuous γ) (hγs : HasCompactSupport γ)
    (hγK : tsupport γ ⊆ K) (hγK' : tsupport γ ⊆ K') :
    E.pairing μ γ = E'.pairing μ γ := by
  haveI := E.finite
  haveI := E.regular
  haveI := E'.finite
  haveI := E'.regular
  set u : PontryaginDual G → ℂ := fourierTransform μ E.e with hudef
  set u' : PontryaginDual G → ℂ := fourierTransform μ E'.e with hu'def
  have huc : Continuous u := E.continuous_transform μ
  have hu'c : Continuous u' := E'.continuous_transform μ
  set γC : PontryaginDual G → ℂ := fun χ => ((γ χ : ℝ) : ℂ) with hγCdef
  have hγCc : Continuous γC := Complex.continuous_ofReal.comp hγc
  have hγCs : HasCompactSupport γC := hγs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hγCsupp : tsupport γC = tsupport γ := by
    unfold tsupport
    congr 1
    ext χ
    simp only [mem_support, hγCdef, ne_eq, Complex.ofReal_eq_zero]
  -- the compactly supported quotient
  have hden : ∀ χ ∈ tsupport γC, u χ * u' χ ≠ 0 := fun χ hχ => by
    rw [hγCsupp] at hχ
    exact mul_ne_zero (E.transform_ne_zero μ (hγK hχ)) (E'.transform_ne_zero μ (hγK' hχ))
  have hbc : Continuous fun χ => γC χ / (u χ * u' χ) :=
    hγCc.div_of_tsupport_ne_zero (huc.mul hu'c) hden
  have hbs : HasCompactSupport fun χ => γC χ / (u χ * u' χ) :=
    hγCs.mono (support_div_subset _ _)
  set B : C₀(PontryaginDual G, ℂ) :=
    ⟨⟨fun χ => γC χ / (u χ * u' χ), hbc⟩, hbs.is_zero_at_infty⟩ with hBdef
  -- the symmetric identity for `B`
  have hsymm := integral_c0_mul_fourierTransform_symm μ (E.cont) (E.supp) (E.σ)
    (E.rep) (E'.integrable μ) (E'.σ) (E'.rep) B
  -- pointwise collapse on both sides
  have hL : ∫ χ, B χ * fourierTransform μ E'.e χ ∂(E.σ) = ∫ χ, γC χ / u χ ∂(E.σ) := by
    refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
    show γC χ / (u χ * u' χ) * u' χ = γC χ / u χ
    by_cases hχ : χ ∈ tsupport γ
    · have hu0 : u χ ≠ 0 := E.transform_ne_zero μ (hγK hχ)
      have hu'0 : u' χ ≠ 0 := E'.transform_ne_zero μ (hγK' hχ)
      field_simp
    · rw [show γC χ = 0 by
        rw [hγCdef]
        simp [image_eq_zero_of_notMem_tsupport hχ], zero_div, zero_div, zero_mul]
  have hR : ∫ χ, B χ * fourierTransform μ E.e χ ∂(E'.σ)
      = ∫ χ, γC χ / u' χ ∂(E'.σ) := by
    refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
    show γC χ / (u χ * u' χ) * u χ = γC χ / u' χ
    by_cases hχ : χ ∈ tsupport γ
    · have hu0 : u χ ≠ 0 := E.transform_ne_zero μ (hγK hχ)
      have hu'0 : u' χ ≠ 0 := E'.transform_ne_zero μ (hγK' hχ)
      field_simp
    · rw [show γC χ = 0 by
        rw [hγCdef]
        simp [image_eq_zero_of_notMem_tsupport hχ], zero_div, zero_div, zero_mul]
  -- convert to real pairings
  have hside : ∀ {K₀ : Set (PontryaginDual G)} (F : AdmissibleSquare μ K₀),
      ∫ χ, γC χ / fourierTransform μ F.e χ ∂(F.σ)
        = ((∫ χ, γ χ / (fourierTransform μ F.e χ).re ∂(F.σ) : ℝ) : ℂ) := by
    intro K₀ F
    rw [show (fun χ => γC χ / fourierTransform μ F.e χ)
        = fun χ => ((γ χ / (fourierTransform μ F.e χ).re : ℝ) : ℂ) from funext fun χ => by
      rw [Complex.ofReal_div, ← F.transform_eq μ χ]]
    exact integral_ofReal
  have hfin : ((E.pairing μ γ : ℝ) : ℂ) = ((E'.pairing μ γ : ℝ) : ℂ) := by
    calc ((E.pairing μ γ : ℝ) : ℂ)
        = ∫ χ, γC χ / u χ ∂(E.σ) := (hside E).symm
      _ = ∫ χ, B χ * fourierTransform μ E'.e χ ∂(E.σ) := hL.symm
      _ = ∫ χ, B χ * fourierTransform μ E.e χ ∂(E'.σ) := hsymm
      _ = ∫ χ, γC χ / u' χ ∂(E'.σ) := hR
      _ = ((E'.pairing μ γ : ℝ) : ℂ) := hside E'
  exact_mod_cast hfin

end AdmissibleSquare

end AdmissibleSquares

/-! ### The dual Haar functional and the dual Haar measure -/

section DualHaar

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- A choice of admissible square for the support of a compactly supported function. -/
noncomputable def dualSquare (γ : C_c(PontryaginDual G, ℝ)) :
    AdmissibleSquare μ (tsupport ⇑γ) :=
  (exists_admissibleSquare μ γ.hasCompactSupport).some

/-- The evaluation of the dual Haar functional against the chosen square only depends on
the function, not on the (admissible) square used to compute it. -/
theorem dualSquare_pairing_eq {K : Set (PontryaginDual G)} (E : AdmissibleSquare μ K)
    (γ : C_c(PontryaginDual G, ℝ)) (hγK : tsupport ⇑γ ⊆ K) :
    (dualSquare μ γ).pairing μ ⇑γ = E.pairing μ ⇑γ :=
  (dualSquare μ γ).pairing_congr μ E (map_continuous γ) γ.hasCompactSupport subset_rfl hγK

/-- **The dual Haar functional** `Λ γ = ∫ χ, γ(χ) / (𝓕e χ).re ∂σₑ`, as a positive linear
functional on `C_c(Ĝ, ℝ)`, where `e` is any admissible square for `tsupport γ`. -/
def dualLambda : C_c(PontryaginDual G, ℝ) →ₚ[ℝ] ℝ where
  toFun := fun γ => (dualSquare μ γ).pairing μ ⇑γ
  map_add' := fun γ δ => by
    have hK : IsCompact (tsupport ⇑γ ∪ tsupport ⇑δ) :=
      γ.hasCompactSupport.union δ.hasCompactSupport
    obtain ⟨E⟩ := exists_admissibleSquare μ hK
    have hγ : tsupport ⇑γ ⊆ tsupport ⇑γ ∪ tsupport ⇑δ := subset_union_left
    have hδ : tsupport ⇑δ ⊆ tsupport ⇑γ ∪ tsupport ⇑δ := subset_union_right
    have hγδ : tsupport ⇑(γ + δ) ⊆ tsupport ⇑γ ∪ tsupport ⇑δ := by
      refine subset_trans ?_ (tsupport_add ⇑γ ⇑δ)
      exact closure_mono fun χ hχ => by
        simp only [mem_support] at hχ ⊢
        exact hχ
    rw [dualSquare_pairing_eq μ E (γ + δ) hγδ, dualSquare_pairing_eq μ E γ hγ,
      dualSquare_pairing_eq μ E δ hδ]
    show ∫ χ, (γ + δ) χ / (fourierTransform μ E.e χ).re ∂E.σ
      = (∫ χ, γ χ / (fourierTransform μ E.e χ).re ∂E.σ)
        + ∫ χ, δ χ / (fourierTransform μ E.e χ).re ∂E.σ
    rw [← integral_add (E.integrable_div_re μ (map_continuous γ) γ.hasCompactSupport hγ)
      (E.integrable_div_re μ (map_continuous δ) δ.hasCompactSupport hδ)]
    refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
    show (γ + δ) χ / (fourierTransform μ E.e χ).re
      = γ χ / (fourierTransform μ E.e χ).re + δ χ / (fourierTransform μ E.e χ).re
    rw [CompactlySupportedContinuousMap.add_apply, add_div]
  map_smul' := fun c γ => by
    have hsub : tsupport ⇑(c • γ) ⊆ tsupport ⇑γ := by
      refine closure_mono fun χ hχ => ?_
      simp only [mem_support, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul] at hχ ⊢
      exact fun h0 => hχ (by rw [h0, mul_zero])
    rw [RingHom.id_apply]
    rw [show (dualSquare μ (c • γ)).pairing μ ⇑(c • γ)
      = (dualSquare μ γ).pairing μ ⇑(c • γ) from
      (dualSquare μ (c • γ)).pairing_congr μ (dualSquare μ γ) (map_continuous _)
        (c • γ).hasCompactSupport subset_rfl hsub]
    show ∫ χ, (c • γ) χ / (fourierTransform μ (dualSquare μ γ).e χ).re
        ∂(dualSquare μ γ).σ
      = c • ∫ χ, γ χ / (fourierTransform μ (dualSquare μ γ).e χ).re ∂(dualSquare μ γ).σ
    rw [smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
    show (c • γ) χ / (fourierTransform μ (dualSquare μ γ).e χ).re
      = c * (γ χ / (fourierTransform μ (dualSquare μ γ).e χ).re)
    rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, mul_div_assoc]
  monotone' := fun γ δ hγδ => by
    have hK : IsCompact (tsupport ⇑γ ∪ tsupport ⇑δ) :=
      γ.hasCompactSupport.union δ.hasCompactSupport
    obtain ⟨E⟩ := exists_admissibleSquare μ hK
    have hγ : tsupport ⇑γ ⊆ tsupport ⇑γ ∪ tsupport ⇑δ := subset_union_left
    have hδ : tsupport ⇑δ ⊆ tsupport ⇑γ ∪ tsupport ⇑δ := subset_union_right
    show (dualSquare μ γ).pairing μ ⇑γ ≤ (dualSquare μ δ).pairing μ ⇑δ
    rw [dualSquare_pairing_eq μ E γ hγ, dualSquare_pairing_eq μ E δ hδ]
    refine integral_mono
      (E.integrable_div_re μ (map_continuous γ) γ.hasCompactSupport hγ)
      (E.integrable_div_re μ (map_continuous δ) δ.hasCompactSupport hδ) fun χ => ?_
    show γ χ / (fourierTransform μ E.e χ).re ≤ δ χ / (fourierTransform μ E.e χ).re
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hγδ χ) (inv_nonneg.mpr (E.transform_nonneg χ))

@[simp]
theorem dualLambda_apply (γ : C_c(PontryaginDual G, ℝ)) :
    dualLambda μ γ = (dualSquare μ γ).pairing μ ⇑γ := rfl

/-- **The dual Haar measure** on the Pontryagin dual, as the Riesz–Markov–Kakutani measure
of the dual Haar functional `dualLambda μ`. -/
def dualHaar : Measure (PontryaginDual G) :=
  RealRMK.rieszMeasure (dualLambda μ)

instance dualHaar_regular : (dualHaar μ).Regular :=
  RealRMK.regular_rieszMeasure _

/-- The dual Haar measure represents the dual Haar functional. -/
theorem integral_cc_dualHaar (γ : C_c(PontryaginDual G, ℝ)) :
    ∫ χ, γ χ ∂(dualHaar μ) = dualLambda μ γ :=
  RealRMK.integral_rieszMeasure _ γ

/-- Integration of a real `C_c` function against the dual Haar measure is computed by the
pairing against **any** admissible square for its support. -/
theorem integral_dualHaar_eq_pairing {K : Set (PontryaginDual G)}
    (E : AdmissibleSquare μ K) {γ : PontryaginDual G → ℝ} (hγc : Continuous γ)
    (hγs : HasCompactSupport γ) (hγK : tsupport γ ⊆ K) :
    ∫ χ, γ χ ∂(dualHaar μ)
      = ∫ χ, γ χ / (fourierTransform μ E.e χ).re ∂E.σ := by
  set γcc : C_c(PontryaginDual G, ℝ) := ⟨⟨γ, hγc⟩, hγs⟩ with hγccdef
  have h1 : ∫ χ, γ χ ∂(dualHaar μ) = dualLambda μ γcc := integral_cc_dualHaar μ γcc
  rw [h1, dualLambda_apply]
  exact (dualSquare μ γcc).pairing_congr μ E hγc hγs subset_rfl hγK

/-- The complex-valued version of `integral_dualHaar_eq_pairing`: integration of a complex
`C_c` function against the dual Haar measure is the integral of the quotient by the (real,
nonvanishing) transform of any admissible square against its Bochner measure. -/
theorem AdmissibleSquare.integral_dualHaar_eq_div {K : Set (PontryaginDual G)}
    (E : AdmissibleSquare μ K) {w : PontryaginDual G → ℂ} (hwc : Continuous w)
    (hws : HasCompactSupport w) (hwK : tsupport w ⊆ K) :
    ∫ χ, w χ ∂(dualHaar μ) = ∫ χ, w χ / fourierTransform μ E.e χ ∂E.σ := by
  haveI := E.finite
  set u : PontryaginDual G → ℂ := fourierTransform μ E.e with hudef
  have huc : Continuous u := E.continuous_transform μ
  have hune : ∀ χ ∈ tsupport w, u χ ≠ 0 := fun χ hχ => E.transform_ne_zero μ (hwK hχ)
  -- real and imaginary parts of `w`
  have hwrec : Continuous fun χ => (w χ).re := Complex.continuous_re.comp hwc
  have hwimc : Continuous fun χ => (w χ).im := Complex.continuous_im.comp hwc
  have hwres : HasCompactSupport fun χ => (w χ).re :=
    hws.comp_left (g := Complex.re) Complex.zero_re
  have hwims : HasCompactSupport fun χ => (w χ).im :=
    hws.comp_left (g := Complex.im) Complex.zero_im
  have hwreK : tsupport (fun χ => (w χ).re) ⊆ K := by
    refine subset_trans (closure_mono fun χ hχ => ?_) hwK
    simp only [mem_support] at hχ ⊢
    exact fun h0 => hχ (by rw [h0, Complex.zero_re])
  have hwimK : tsupport (fun χ => (w χ).im) ⊆ K := by
    refine subset_trans (closure_mono fun χ hχ => ?_) hwK
    simp only [mem_support] at hχ ⊢
    exact fun h0 => hχ (by rw [h0, Complex.zero_im])
  -- integrability on both sides
  have hwint : Integrable w (dualHaar μ) := hwc.integrable_of_hasCompactSupport hws
  have hdivc : Continuous fun χ => w χ / u χ := hwc.div_of_tsupport_ne_zero huc hune
  have hdivs : HasCompactSupport fun χ => w χ / u χ := hws.mono (support_div_subset _ _)
  have hdivint : Integrable (fun χ => w χ / u χ) E.σ :=
    hdivc.integrable_of_hasCompactSupport hdivs
  -- the pointwise real/imaginary parts of the quotient
  have hueq : ∀ χ, u χ = (((u χ).re : ℝ) : ℂ) := fun χ => E.transform_eq μ χ
  have hptre : ∀ χ, (w χ / u χ).re = (w χ).re / (u χ).re := fun χ => by
    conv_lhs => rw [hueq χ]
    exact Complex.div_ofReal_re _ _
  have hptim : ∀ χ, (w χ / u χ).im = (w χ).im / (u χ).re := fun χ => by
    conv_lhs => rw [hueq χ]
    exact Complex.div_ofReal_im _ _
  refine Complex.ext ?_ ?_
  · calc (∫ χ, w χ ∂(dualHaar μ)).re
        = ∫ χ, (w χ).re ∂(dualHaar μ) := by
          simp_rw [← RCLike.re_to_complex]
          exact (integral_re hwint).symm
      _ = ∫ χ, (w χ).re / (u χ).re ∂E.σ :=
          integral_dualHaar_eq_pairing μ E hwrec hwres hwreK
      _ = ∫ χ, (w χ / u χ).re ∂E.σ :=
          integral_congr_ae (Eventually.of_forall fun χ => (hptre χ).symm)
      _ = (∫ χ, w χ / u χ ∂E.σ).re := by
          simp_rw [← RCLike.re_to_complex]
          exact integral_re hdivint
  · calc (∫ χ, w χ ∂(dualHaar μ)).im
        = ∫ χ, (w χ).im ∂(dualHaar μ) := by
          simp_rw [← RCLike.im_to_complex]
          exact (integral_im hwint).symm
      _ = ∫ χ, (w χ).im / (u χ).re ∂E.σ :=
          integral_dualHaar_eq_pairing μ E hwimc hwims hwimK
      _ = ∫ χ, (w χ / u χ).im ∂E.σ :=
          integral_congr_ae (Eventually.of_forall fun χ => (hptim χ).symm)
      _ = (∫ χ, w χ / u χ ∂E.σ).im := by
          simp_rw [← RCLike.im_to_complex]
          exact integral_im hdivint

/-! ### Translation invariance -/

/-- Invariance of the dual Haar functional under translation of the argument, proved by
transporting an admissible square along the modulation `AdmissibleSquare.mulChar`. -/
theorem integral_comp_mulLeft_dualHaar {γ : PontryaginDual G → ℝ} (hγc : Continuous γ)
    (hγs : HasCompactSupport γ) (η : PontryaginDual G) :
    ∫ χ, γ (η * χ) ∂(dualHaar μ) = ∫ χ, γ χ ∂(dualHaar μ) := by
  have hγηc : Continuous fun χ : PontryaginDual G => γ (η * χ) :=
    hγc.comp (continuous_const.mul continuous_id)
  have hsupp : tsupport (fun χ : PontryaginDual G => γ (η * χ))
      = ⇑(Homeomorph.mulLeft η) ⁻¹' tsupport γ := by
    rw [show (fun χ : PontryaginDual G => γ (η * χ)) = γ ∘ ⇑(Homeomorph.mulLeft η) from rfl]
    exact tsupport_comp_eq_preimage γ (Homeomorph.mulLeft η)
  have hγηs : HasCompactSupport fun χ : PontryaginDual G => γ (η * χ) := by
    show IsCompact (tsupport fun χ : PontryaginDual G => γ (η * χ))
    rw [hsupp]
    exact (Homeomorph.mulLeft η).isCompact_preimage.mpr hγs
  obtain ⟨E⟩ := exists_admissibleSquare μ
    (hγηs : IsCompact (tsupport fun χ : PontryaginDual G => γ (η * χ)))
  haveI := E.finite
  -- `tsupport γ` is contained in the compact set of the modulated square
  have himg : tsupport γ ⊆ (η * ·) '' (tsupport fun χ : PontryaginDual G => γ (η * χ)) := by
    intro χ hχ
    refine ⟨η⁻¹ * χ, ?_, by show η * (η⁻¹ * χ) = χ; rw [mul_inv_cancel_left]⟩
    rw [hsupp]
    show (Homeomorph.mulLeft η) (η⁻¹ * χ) ∈ tsupport γ
    rw [show (Homeomorph.mulLeft η) (η⁻¹ * χ) = η * (η⁻¹ * χ) from rfl, mul_inv_cancel_left]
    exact hχ
  rw [integral_dualHaar_eq_pairing μ (E.mulChar μ η) hγc hγs himg,
    integral_dualHaar_eq_pairing μ E hγηc hγηs subset_rfl]
  show ∫ χ, γ (η * χ) / (fourierTransform μ E.e χ).re ∂E.σ
    = ∫ χ, γ χ / (fourierTransform μ (E.mulChar μ η).e χ).re ∂(E.mulChar μ η).σ
  have h1 : ∫ χ, γ χ / (fourierTransform μ (E.mulChar μ η).e χ).re ∂(E.mulChar μ η).σ
      = ∫ ψ, γ ((Homeomorph.mulLeft η).toMeasurableEquiv ψ)
          / (fourierTransform μ (E.mulChar μ η).e
              ((Homeomorph.mulLeft η).toMeasurableEquiv ψ)).re ∂E.σ :=
    MeasureTheory.integral_map_equiv _ _
  rw [h1]
  refine integral_congr_ae (Eventually.of_forall fun ψ => ?_)
  show γ (η * ψ) / (fourierTransform μ E.e ψ).re
    = γ (η * ψ) / (fourierTransform μ (E.mulChar μ η).e (η * ψ)).re
  rw [E.mulChar_transform μ η (η * ψ), mul_div_cancel_left]

instance dualHaar_isMulLeftInvariant : (dualHaar μ).IsMulLeftInvariant := by
  refine ⟨fun η => ?_⟩
  have hcoe : ((η * ·) : PontryaginDual G → PontryaginDual G)
      = ⇑(Homeomorph.mulLeft η).toMeasurableEquiv := by
    rw [Homeomorph.toMeasurableEquiv_coe, Homeomorph.coe_mulLeft]
  haveI : (Measure.map (η * ·) (dualHaar μ)).Regular := by
    rw [show Measure.map (η * ·) (dualHaar μ)
        = Measure.map (⇑(Homeomorph.mulLeft η)) (dualHaar μ) by
      rw [Homeomorph.coe_mulLeft]]
    exact Measure.Regular.map (Homeomorph.mulLeft η)
  refine Measure.ext_of_integral_eq_on_compactlySupported fun γ => ?_
  have h1 : ∫ χ, γ χ ∂(Measure.map (η * ·) (dualHaar μ))
      = ∫ χ, γ (η * χ) ∂(dualHaar μ) := by
    rw [hcoe]
    exact MeasureTheory.integral_map_equiv _ _
  rw [h1]
  exact integral_comp_mulLeft_dualHaar μ (map_continuous γ) γ.hasCompactSupport η

end DualHaar

/-! ### The density identity -/

section DensityIdentity

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- **The density identity.**  For `f` integrable with Bochner measure `σ_f` and every
complex `C_c` function `a` on the dual group,

`∫ χ, a(χ) ⬝ 𝓕f(χ) ∂(dualHaar μ) = ∫ χ, a(χ) ∂σ_f`.

This identifies `dualHaar μ` as the measure for which `𝓕f` is the density of `σ_f`. -/
theorem integral_cc_mul_fourierTransform_dualHaar
    (σf : Measure (PontryaginDual G)) [IsFiniteMeasure σf] [σf.InnerRegularCompactLTTop]
    {f : G → ℂ} (hfi : Integrable f μ) (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf)
    {a : PontryaginDual G → ℂ} (hac : Continuous a) (has : HasCompactSupport a) :
    ∫ χ, a χ * fourierTransform μ f χ ∂(dualHaar μ) = ∫ χ, a χ ∂σf := by
  obtain ⟨E⟩ := exists_admissibleSquare μ (has : IsCompact (tsupport a))
  haveI := E.finite
  haveI := E.regular
  have huc : Continuous (fourierTransform μ E.e) := E.continuous_transform μ
  have hune : ∀ χ ∈ tsupport a, fourierTransform μ E.e χ ≠ 0 := fun χ hχ =>
    E.transform_ne_zero μ hχ
  have hfour_c : Continuous (fourierTransform μ f) := continuous_fourierTransform μ hfi
  -- the compactly supported quotient `b = a / 𝓕e`
  have hbc : Continuous fun χ => a χ / fourierTransform μ E.e χ :=
    hac.div_of_tsupport_ne_zero huc hune
  have hbs : HasCompactSupport fun χ => a χ / fourierTransform μ E.e χ :=
    has.mono (support_div_subset _ _)
  set B : C₀(PontryaginDual G, ℂ) :=
    ⟨⟨fun χ => a χ / fourierTransform μ E.e χ, hbc⟩, hbs.is_zero_at_infty⟩ with hBdef
  -- Step 1: complex evaluation of the `C_c` function `a ⬝ 𝓕f` against `dualHaar μ`
  have h1 : ∫ χ, a χ * fourierTransform μ f χ ∂(dualHaar μ)
      = ∫ χ, (a χ * fourierTransform μ f χ) / fourierTransform μ E.e χ ∂E.σ := by
    refine E.integral_dualHaar_eq_div μ (hac.mul hfour_c) has.mul_right ?_
    exact tsupport_mul_subset_left
  -- Step 2: pointwise rearrangement
  have h2 : ∫ χ, (a χ * fourierTransform μ f χ) / fourierTransform μ E.e χ ∂E.σ
      = ∫ χ, B χ * fourierTransform μ f χ ∂E.σ := by
    refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
    show (a χ * fourierTransform μ f χ) / fourierTransform μ E.e χ
      = a χ / fourierTransform μ E.e χ * fourierTransform μ f χ
    rw [mul_div_right_comm]
  -- Step 3: the symmetric identity
  have h3 : ∫ χ, B χ * fourierTransform μ f χ ∂E.σ
      = ∫ χ, B χ * fourierTransform μ E.e χ ∂σf :=
    integral_c0_mul_fourierTransform_symm μ E.cont E.supp E.σ E.rep hfi σf hrep B
  -- Step 4: collapse the quotient
  have h4 : ∫ χ, B χ * fourierTransform μ E.e χ ∂σf = ∫ χ, a χ ∂σf := by
    refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
    show a χ / fourierTransform μ E.e χ * fourierTransform μ E.e χ = a χ
    by_cases hχ : fourierTransform μ E.e χ = 0
    · have ha0 : a χ = 0 := by
        by_contra hane
        exact hune χ (subset_tsupport a (mem_support.mpr hane)) hχ
      rw [ha0, zero_div, zero_mul]
    · rw [div_mul_cancel₀ _ hχ]
  rw [h1, h2, h3, h4]

end DensityIdentity

/-! ### The dual Haar measure is a Haar measure -/

section HaarInstances

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

instance dualHaar_neZero : NeZero (dualHaar μ) := by
  constructor
  intro h0
  -- an admissible square with nonzero Bochner measure
  obtain ⟨E⟩ := exists_admissibleSquare μ
    (isCompact_singleton : IsCompact ({1} : Set (PontryaginDual G)))
  haveI := E.finite
  haveI := E.regular
  -- a compact set of positive `σ`-measure and a Urysohn function above it
  obtain ⟨Q, hQcomp, hQne⟩ := MeasureTheory.Measure.Regular.exists_isCompact_not_null.mpr
    E.ne_zero
  obtain ⟨a, ha1, -, has, ha01⟩ :=
    exists_continuous_one_zero_of_isCompact hQcomp isClosed_empty (Set.disjoint_empty Q)
  have haC : Continuous fun χ : PontryaginDual G => ((a χ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp a.continuous
  have haCs : HasCompactSupport fun χ : PontryaginDual G => ((a χ : ℝ) : ℂ) :=
    has.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  -- the density identity for `f = E.e`
  have h6 := integral_cc_mul_fourierTransform_dualHaar μ E.σ (E.integrable μ) E.rep haC haCs
  rw [h0] at h6
  simp only [integral_zero_measure] at h6
  -- but `∫ a ∂σ ≥ σ.real Q > 0`
  have haint : Integrable (⇑a) E.σ := a.continuous.integrable_of_hasCompactSupport has
  have hge : E.σ.real Q ≤ ∫ χ, a χ ∂E.σ := by
    calc E.σ.real Q = ∫ _χ in Q, (1 : ℝ) ∂E.σ := by
          rw [setIntegral_const, smul_eq_mul, mul_one]
      _ = ∫ χ in Q, a χ ∂E.σ := by
          refine (setIntegral_congr_fun hQcomp.measurableSet fun χ hχ => ?_).symm
          exact ha1 hχ
      _ ≤ ∫ χ, a χ ∂E.σ :=
          setIntegral_le_integral haint (Eventually.of_forall fun χ => (ha01 χ).1)
  have hQpos : 0 < E.σ.real Q :=
    ENNReal.toReal_pos hQne (measure_ne_top E.σ Q)
  have hcast : ((∫ χ, a χ ∂E.σ : ℝ) : ℂ) = 0 := by
    rw [← h6.symm]
    exact (show ∫ χ, ((a χ : ℝ) : ℂ) ∂E.σ = ((∫ χ, a χ ∂E.σ : ℝ) : ℂ) from
      integral_ofReal).symm
  have : (∫ χ, a χ ∂E.σ : ℝ) = 0 := by exact_mod_cast hcast
  linarith

instance dualHaar_isOpenPosMeasure : (dualHaar μ).IsOpenPosMeasure :=
  isOpenPosMeasure_of_mulLeftInvariant_of_regular

instance dualHaar_isHaarMeasure : (dualHaar μ).IsHaarMeasure :=
  { lt_top_of_isCompact := fun _K hK => hK.measure_lt_top
    toIsMulLeftInvariant := dualHaar_isMulLeftInvariant μ
    toIsOpenPosMeasure := dualHaar_isOpenPosMeasure μ }

end HaarInstances

/-! ### The Fourier transform of a positive-type function is real and nonnegative -/

section TransformReal

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- A function of positive type is invariant under the star involution. -/
theorem IsPositiveType.mstar_eq {f : G → ℂ} (hf : IsPositiveType f) : mstar f = f :=
  funext fun x => by rw [mstar_apply, hf.apply_inv x, Complex.conj_conj]

/-- The Fourier transform of a function of positive type is real. -/
theorem IsPositiveType.fourierTransform_im {f : G → ℂ} (hf : IsPositiveType f)
    (χ : PontryaginDual G) : (fourierTransform μ f χ).im = 0 := by
  have h := fourierTransform_mstar μ f χ
  rw [hf.mstar_eq] at h
  exact Complex.conj_eq_iff_im.mp h.symm

variable (σf : Measure (PontryaginDual G)) [IsFiniteMeasure σf]
  [σf.InnerRegularCompactLTTop] {f : G → ℂ}

/-- **The real form of the density identity**: for real `C_c` functions `a`,
`∫ χ, a(χ) ⬝ (𝓕f χ).re ∂(dualHaar μ) = ∫ χ, a(χ) ∂σ_f`. -/
theorem integral_cc_mul_re_fourierTransform_dualHaar (hfi : Integrable f μ)
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf)
    {a : PontryaginDual G → ℝ} (hac : Continuous a) (has : HasCompactSupport a) :
    ∫ χ, a χ * (fourierTransform μ f χ).re ∂(dualHaar μ) = ∫ χ, a χ ∂σf := by
  have haC : Continuous fun χ : PontryaginDual G => ((a χ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hac
  have haCs : HasCompactSupport fun χ : PontryaginDual G => ((a χ : ℝ) : ℂ) :=
    has.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have h6 := integral_cc_mul_fourierTransform_dualHaar μ σf hfi hrep haC haCs
  have hint : Integrable (fun χ => ((a χ : ℝ) : ℂ) * fourierTransform μ f χ) (dualHaar μ) :=
    (haC.mul (continuous_fourierTransform μ hfi)).integrable_of_hasCompactSupport
      haCs.mul_right
  calc ∫ χ, a χ * (fourierTransform μ f χ).re ∂(dualHaar μ)
      = ∫ χ, (((a χ : ℝ) : ℂ) * fourierTransform μ f χ).re ∂(dualHaar μ) := by
        refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
        show a χ * (fourierTransform μ f χ).re = (((a χ : ℝ) : ℂ) * fourierTransform μ f χ).re
        rw [Complex.re_ofReal_mul]
    _ = (∫ χ, ((a χ : ℝ) : ℂ) * fourierTransform μ f χ ∂(dualHaar μ)).re := by
        simp_rw [← RCLike.re_to_complex]
        exact integral_re hint
    _ = (∫ χ, ((a χ : ℝ) : ℂ) ∂σf).re := by rw [h6]
    _ = ∫ χ, a χ ∂σf := by
        rw [show ∫ χ, ((a χ : ℝ) : ℂ) ∂σf = ((∫ χ, a χ ∂σf : ℝ) : ℂ) from integral_ofReal,
          Complex.ofReal_re]

/-- **Nonnegativity of the transform**: the Fourier transform of a function with a Bochner
representation is (real and) nonnegative. -/
theorem fourierTransform_re_nonneg (hfi : Integrable f μ)
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf) (χ : PontryaginDual G) :
    0 ≤ (fourierTransform μ f χ).re := by
  have hFc : Continuous fun χ => (fourierTransform μ f χ).re :=
    Complex.continuous_re.comp (continuous_fourierTransform μ hfi)
  refine hFc.nonneg_of_forall_integral_cc_nonneg (dualHaar μ) (fun a hac has ha0 => ?_) χ
  rw [integral_cc_mul_re_fourierTransform_dualHaar μ σf hfi hrep hac has]
  exact integral_nonneg ha0

/-- The Fourier transform of a function with a Bochner representation coincides with the
coercion of its real part. -/
theorem fourierTransform_eq_ofReal_re
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf) (χ : PontryaginDual G) :
    fourierTransform μ f χ = (((fourierTransform μ f χ).re : ℝ) : ℂ) := by
  have hpt : IsPositiveType f := by
    rw [show f = fun x => ∫ χ, (χ x : ℂ) ∂σf from funext hrep]
    exact isPositiveType_integral_char σf
  exact Complex.ext (Complex.ofReal_re _).symm
    (by rw [Complex.ofReal_im, hpt.fourierTransform_im μ χ])

/-- The `C_c` cutoffs capture almost all the mass of a finite regular measure: for `ε > 0`
there is a `C_c` function `0 ≤ a ≤ 1` with `∫ a ∂σ_f ≥ σ_f(Ĝ) - ε` (with the support
control needed for the tail estimates). -/
theorem exists_cutoff_integral_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ a : PontryaginDual G → ℝ, Continuous a ∧ HasCompactSupport a ∧
      (∀ χ, 0 ≤ a χ ∧ a χ ≤ 1) ∧ σf.real Set.univ - ε ≤ ∫ χ, a χ ∂σf := by
  obtain ⟨Q, -, hQcomp, hQlt⟩ := MeasurableSet.univ.exists_isCompact_lt_add
    (μ := σf) (measure_ne_top σf _) (by positivity : ENNReal.ofReal ε ≠ 0)
  obtain ⟨a, ha1, -, has, ha01⟩ :=
    exists_continuous_one_zero_of_isCompact hQcomp isClosed_empty (Set.disjoint_empty Q)
  have haint : Integrable (⇑a) σf := a.continuous.integrable_of_hasCompactSupport has
  refine ⟨⇑a, a.continuous, has, ha01, ?_⟩
  have h1 : σf.real Q ≤ ∫ χ, a χ ∂σf := by
    calc σf.real Q = ∫ _χ in Q, (1 : ℝ) ∂σf := by
          rw [setIntegral_const, smul_eq_mul, mul_one]
      _ = ∫ χ in Q, a χ ∂σf := by
          refine (setIntegral_congr_fun hQcomp.measurableSet fun χ hχ => ?_).symm
          exact ha1 hχ
      _ ≤ ∫ χ, a χ ∂σf :=
          setIntegral_le_integral haint (Eventually.of_forall fun χ => (ha01 χ).1)
  have h2 : σf.real Set.univ - ε ≤ σf.real Q := by
    have h3 : σf Set.univ ≤ σf Q + ENNReal.ofReal ε := hQlt.le
    have h4 : σf.real Set.univ ≤ σf.real Q + ε := by
      calc σf.real Set.univ ≤ (σf Q + ENNReal.ofReal ε).toReal :=
            ENNReal.toReal_mono (by finiteness) h3
        _ = σf.real Q + ε := by
            rw [ENNReal.toReal_add (measure_ne_top σf Q) ENNReal.ofReal_ne_top,
              ENNReal.toReal_ofReal hε.le]
            rfl
    linarith
  linarith

end TransformReal

/-! ### Integrability and total mass of the transform -/

section TransformIntegrable

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
variable (σf : Measure (PontryaginDual G)) [IsFiniteMeasure σf]
  [σf.InnerRegularCompactLTTop] {f : G → ℂ}

/-- The compact-set bound: `∫⁻_Q (𝓕f).re ∂(dualHaar μ) ≤ σ_f(Ĝ)` for every compact `Q`. -/
private theorem setLIntegral_re_fourierTransform_compact_le (hfi : Integrable f μ)
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf) {Q : Set (PontryaginDual G)}
    (hQ : IsCompact Q) :
    ∫⁻ χ in Q, ENNReal.ofReal ((fourierTransform μ f χ).re) ∂(dualHaar μ)
      ≤ ENNReal.ofReal (σf.real Set.univ) := by
  obtain ⟨a, ha1, -, has, ha01⟩ :=
    exists_continuous_one_zero_of_isCompact hQ isClosed_empty (Set.disjoint_empty Q)
  have hF0 : ∀ χ, 0 ≤ (fourierTransform μ f χ).re :=
    fourierTransform_re_nonneg μ σf hfi hrep
  have hFc : Continuous fun χ => (fourierTransform μ f χ).re :=
    Complex.continuous_re.comp (continuous_fourierTransform μ hfi)
  have haF_int : Integrable (fun χ => a χ * (fourierTransform μ f χ).re) (dualHaar μ) :=
    (a.continuous.mul hFc).integrable_of_hasCompactSupport has.mul_right
  calc ∫⁻ χ in Q, ENNReal.ofReal ((fourierTransform μ f χ).re) ∂(dualHaar μ)
      ≤ ∫⁻ χ, ENNReal.ofReal (a χ * (fourierTransform μ f χ).re) ∂(dualHaar μ) := by
        rw [← lintegral_indicator hQ.measurableSet]
        refine lintegral_mono fun χ => ?_
        by_cases hχ : χ ∈ Q
        · rw [Set.indicator_of_mem hχ, show a χ = 1 from ha1 hχ, one_mul]
        · rw [Set.indicator_of_notMem hχ]
          exact zero_le
    _ = ENNReal.ofReal (∫ χ, a χ * (fourierTransform μ f χ).re ∂(dualHaar μ)) :=
        (ofReal_integral_eq_lintegral_ofReal haF_int
          (Eventually.of_forall fun χ => mul_nonneg (ha01 χ).1 (hF0 χ))).symm
    _ ≤ ENNReal.ofReal (σf.real Set.univ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_cc_mul_re_fourierTransform_dualHaar μ σf hfi hrep a.continuous has]
        calc ∫ χ, a χ ∂σf
            ≤ ∫ _χ, (1 : ℝ) ∂σf :=
              integral_mono (a.continuous.integrable_of_hasCompactSupport has)
                (integrable_const 1) fun χ => (ha01 χ).2
          _ = σf.real Set.univ := by rw [integral_const, smul_eq_mul, mul_one]

/-- The weak bound: the super-level sets of `(𝓕f).re` have finite dual Haar measure. -/
private theorem measure_lt_re_fourierTransform_le (hfi : Integrable f μ)
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf) {t : ℝ} (ht : 0 < t) :
    (dualHaar μ) {χ | t < (fourierTransform μ f χ).re}
      ≤ ENNReal.ofReal (σf.real Set.univ) / ENNReal.ofReal t := by
  have hFc : Continuous fun χ => (fourierTransform μ f χ).re :=
    Complex.continuous_re.comp (continuous_fourierTransform μ hfi)
  have hopen : IsOpen {χ : PontryaginDual G | t < (fourierTransform μ f χ).re} :=
    isOpen_lt continuous_const hFc
  by_contra hcon
  push Not at hcon
  obtain ⟨Q, hQsub, hQcomp, hQlt⟩ := hopen.exists_lt_isCompact hcon
  have h1 : ENNReal.ofReal t * (dualHaar μ) Q ≤ ENNReal.ofReal (σf.real Set.univ) := by
    calc ENNReal.ofReal t * (dualHaar μ) Q
        = ∫⁻ _χ in Q, ENNReal.ofReal t ∂(dualHaar μ) := (setLIntegral_const Q _).symm
      _ ≤ ∫⁻ χ in Q, ENNReal.ofReal ((fourierTransform μ f χ).re) ∂(dualHaar μ) :=
          setLIntegral_mono' hQcomp.measurableSet fun χ hχ =>
            ENNReal.ofReal_le_ofReal (hQsub hχ).le
      _ ≤ ENNReal.ofReal (σf.real Set.univ) :=
          setLIntegral_re_fourierTransform_compact_le μ σf hfi hrep hQcomp
  have h2 : (dualHaar μ) Q ≤ ENNReal.ofReal (σf.real Set.univ) / ENNReal.ofReal t := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr ht).ne')
      (Or.inl ENNReal.ofReal_ne_top)]
    rwa [mul_comm] at h1
  exact absurd h2 (not_le.mpr hQlt)

/-- **The lintegral bound**: `∫⁻ (𝓕f).re ∂(dualHaar μ) ≤ σ_f(Ĝ)`.  The proof exhausts
`{𝓕f > 0}` by the open super-level sets `{𝓕f > 1/(n+1)}`, which have finite dual Haar
measure by the weak bound, and controls each of them via inner regularity and the
compact-set bound. -/
theorem lintegral_ofReal_re_fourierTransform_dualHaar_le (hfi : Integrable f μ)
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf) :
    ∫⁻ χ, ENNReal.ofReal ((fourierTransform μ f χ).re) ∂(dualHaar μ)
      ≤ ENNReal.ofReal (σf.real Set.univ) := by
  have hFc : Continuous fun χ => (fourierTransform μ f χ).re :=
    Complex.continuous_re.comp (continuous_fourierTransform μ hfi)
  have hF0 : ∀ χ, 0 ≤ (fourierTransform μ f χ).re :=
    fourierTransform_re_nonneg μ σf hfi hrep
  set C : ℝ := ∫ x, ‖f x‖ ∂μ with hCdef
  have hFC : ∀ χ, (fourierTransform μ f χ).re ≤ C := fun χ =>
    ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans (norm_fourierTransform_le μ f χ)
  set g : PontryaginDual G → ℝ≥0∞ := fun χ => ENNReal.ofReal ((fourierTransform μ f χ).re)
    with hgdef
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp hFc.measurable
  set U : ℕ → Set (PontryaginDual G) :=
    fun n => {χ | ((n : ℝ) + 1)⁻¹ < (fourierTransform μ f χ).re} with hUdef
  have hUopen : ∀ n, IsOpen (U n) := fun n => isOpen_lt continuous_const hFc
  have hUmono : Monotone U := by
    intro a b hab χ hχ
    have h1 : ((b : ℝ) + 1)⁻¹ ≤ ((a : ℝ) + 1)⁻¹ := by
      have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      have hab1 : ((a : ℝ) + 1) ≤ (b : ℝ) + 1 := by
        have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
        linarith
      exact inv_anti₀ ha1 hab1
    exact lt_of_le_of_lt h1 hχ
  have hUfin : ∀ n, (dualHaar μ) (U n) ≠ ∞ := by
    intro n
    have hbound := measure_lt_re_fourierTransform_le μ σf hfi hrep
      (t := ((n : ℝ) + 1)⁻¹) (by positivity)
    exact ne_top_of_le_ne_top
      (ENNReal.div_lt_top ENNReal.ofReal_ne_top
        (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)).ne').ne hbound
  -- the pointwise supremum identity
  have hsup : ∀ χ, g χ = ⨆ n, (U n).indicator g χ := by
    intro χ
    rcases eq_or_lt_of_le (hF0 χ) with h0 | hpos
    · have hg0 : g χ = 0 := by
        rw [hgdef]
        simp [← h0]
      have hnot : ∀ n, χ ∉ U n := fun n hn => by
        rw [hUdef] at hn
        have : ((n : ℝ) + 1)⁻¹ < (fourierTransform μ f χ).re := hn
        rw [← h0] at this
        have hp : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
        linarith
      simp [Set.indicator_of_notMem (hnot _), hg0]
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      have hmem : χ ∈ U n := by
        rw [hUdef]
        show ((n : ℝ) + 1)⁻¹ < (fourierTransform μ f χ).re
        rw [← one_div]
        exact hn
      refine le_antisymm ?_ ?_
      · exact le_iSup_of_le n (le_of_eq (Set.indicator_of_mem hmem g).symm)
      · refine iSup_le fun m => ?_
        by_cases hm : χ ∈ U m
        · rw [Set.indicator_of_mem hm]
        · rw [Set.indicator_of_notMem hm]
          exact zero_le
  have hmeas' : ∀ n, Measurable ((U n).indicator g) := fun n =>
    hgm.indicator (hUopen n).measurableSet
  have hmono' : Monotone fun n => (U n).indicator g := by
    intro a b hab χ
    show (U a).indicator g χ ≤ (U b).indicator g χ
    by_cases hχ : χ ∈ U a
    · rw [Set.indicator_of_mem hχ, Set.indicator_of_mem (hUmono hab hχ)]
    · rw [Set.indicator_of_notMem hχ]
      exact zero_le
  -- each super-level set carries at most the total mass
  have hUn_le : ∀ n, ∫⁻ χ in U n, g χ ∂(dualHaar μ) ≤ ENNReal.ofReal (σf.real Set.univ) := by
    intro n
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _hlt => ?_
    set ε' : ℝ≥0∞ := (ε : ℝ≥0∞) / (ENNReal.ofReal C + 1) with hε'def
    have hden0 : (ENNReal.ofReal C + 1 : ℝ≥0∞) ≠ 0 := by simp
    have hdent : (ENNReal.ofReal C + 1 : ℝ≥0∞) ≠ ∞ := by
      simp [ENNReal.ofReal_ne_top]
    have hε'0 : ε' ≠ 0 := by
      rw [hε'def]
      simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
      exact ⟨by exact_mod_cast hε.ne', hdent⟩
    obtain ⟨Q, hQsub, hQcomp, hQlt⟩ :=
      (hUopen n).measurableSet.exists_isCompact_lt_add (hUfin n) hε'0
    have hdiff : (dualHaar μ) (U n \ Q) < ε' :=
      measure_sdiff_lt_of_lt_add hQcomp.measurableSet.nullMeasurableSet hQsub
        (ne_top_of_le_ne_top (hUfin n) (measure_mono hQsub)) hQlt
    calc ∫⁻ χ in U n, g χ ∂(dualHaar μ)
        = ∫⁻ χ in Q ∪ (U n \ Q), g χ ∂(dualHaar μ) := by
          rw [Set.union_sdiff_cancel hQsub]
      _ = ∫⁻ χ in Q, g χ ∂(dualHaar μ) + ∫⁻ χ in U n \ Q, g χ ∂(dualHaar μ) :=
          lintegral_union ((hUopen n).measurableSet.diff hQcomp.measurableSet)
            Set.disjoint_sdiff_right
      _ ≤ ENNReal.ofReal (σf.real Set.univ) + ENNReal.ofReal C * ε' := by
          refine add_le_add
            (setLIntegral_re_fourierTransform_compact_le μ σf hfi hrep hQcomp) ?_
          calc ∫⁻ χ in U n \ Q, g χ ∂(dualHaar μ)
              ≤ ∫⁻ _χ in U n \ Q, ENNReal.ofReal C ∂(dualHaar μ) :=
                setLIntegral_mono' ((hUopen n).measurableSet.diff hQcomp.measurableSet)
                  fun χ _ => ENNReal.ofReal_le_ofReal (hFC χ)
            _ = ENNReal.ofReal C * (dualHaar μ) (U n \ Q) := setLIntegral_const _ _
            _ ≤ ENNReal.ofReal C * ε' := mul_le_mul_right hdiff.le _
      _ ≤ ENNReal.ofReal (σf.real Set.univ) + (ε : ℝ≥0∞) := by
          refine add_le_add le_rfl ?_
          calc ENNReal.ofReal C * ε'
              ≤ (ENNReal.ofReal C + 1) * ε' := mul_le_mul_left le_self_add _
            _ = (ε : ℝ≥0∞) := by
                rw [hε'def]
                exact ENNReal.mul_div_cancel hden0 hdent
  calc ∫⁻ χ, g χ ∂(dualHaar μ)
      = ∫⁻ χ, ⨆ n, (U n).indicator g χ ∂(dualHaar μ) := lintegral_congr hsup
    _ = ⨆ n, ∫⁻ χ, (U n).indicator g χ ∂(dualHaar μ) := lintegral_iSup hmeas' hmono'
    _ = ⨆ n, ∫⁻ χ in U n, g χ ∂(dualHaar μ) := by
        refine iSup_congr fun n => ?_
        exact lintegral_indicator (hUopen n).measurableSet g
    _ ≤ ENNReal.ofReal (σf.real Set.univ) := iSup_le hUn_le

/-- The real part of the transform is integrable against the dual Haar measure. -/
theorem integrable_re_fourierTransform_dualHaar (hfi : Integrable f μ)
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf) :
    Integrable (fun χ => (fourierTransform μ f χ).re) (dualHaar μ) := by
  have hFc : Continuous fun χ => (fourierTransform μ f χ).re :=
    Complex.continuous_re.comp (continuous_fourierTransform μ hfi)
  have hF0 : ∀ χ, 0 ≤ (fourierTransform μ f χ).re :=
    fourierTransform_re_nonneg μ σf hfi hrep
  refine ⟨hFc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hF0)]
  exact lt_of_le_of_lt (lintegral_ofReal_re_fourierTransform_dualHaar_le μ σf hfi hrep)
    ENNReal.ofReal_lt_top

/-- **Integrability of the transform**: for `f` integrable with a Bochner representation,
`𝓕f` is integrable against the dual Haar measure. -/
theorem integrable_fourierTransform_dualHaar (hfi : Integrable f μ)
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf) :
    Integrable (fourierTransform μ f) (dualHaar μ) := by
  rw [show fourierTransform μ f = fun χ => (((fourierTransform μ f χ).re : ℝ) : ℂ) from
    funext (fourierTransform_eq_ofReal_re μ σf hrep)]
  exact (integrable_re_fourierTransform_dualHaar μ σf hfi hrep).ofReal

/-- **The total mass identity, real form**: `∫ (𝓕f).re ∂(dualHaar μ) = σ_f(Ĝ)`. -/
theorem integral_re_fourierTransform_dualHaar (hfi : Integrable f μ)
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf) :
    ∫ χ, (fourierTransform μ f χ).re ∂(dualHaar μ) = σf.real Set.univ := by
  have hFc : Continuous fun χ => (fourierTransform μ f χ).re :=
    Complex.continuous_re.comp (continuous_fourierTransform μ hfi)
  have hF0 : ∀ χ, 0 ≤ (fourierTransform μ f χ).re :=
    fourierTransform_re_nonneg μ σf hfi hrep
  have hS0 : 0 ≤ σf.real Set.univ := measureReal_nonneg
  have hFint := integrable_re_fourierTransform_dualHaar μ σf hfi hrep
  refine le_antisymm ?_ ?_
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0)
      hFc.aestronglyMeasurable]
    calc (∫⁻ χ, ENNReal.ofReal ((fourierTransform μ f χ).re) ∂(dualHaar μ)).toReal
        ≤ (ENNReal.ofReal (σf.real Set.univ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top
            (lintegral_ofReal_re_fourierTransform_dualHaar_le μ σf hfi hrep)
      _ = σf.real Set.univ := ENNReal.toReal_ofReal hS0
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨a, hac, has, ha01, hage⟩ := exists_cutoff_integral_ge σf hε
    have hclaimA := integral_cc_mul_re_fourierTransform_dualHaar μ σf hfi hrep hac has
    have haF_int : Integrable (fun χ => a χ * (fourierTransform μ f χ).re) (dualHaar μ) :=
      (hac.mul hFc).integrable_of_hasCompactSupport has.mul_right
    have hle : ∫ χ, a χ * (fourierTransform μ f χ).re ∂(dualHaar μ)
        ≤ ∫ χ, (fourierTransform μ f χ).re ∂(dualHaar μ) := by
      refine integral_mono haF_int hFint fun χ => ?_
      calc a χ * (fourierTransform μ f χ).re
          ≤ 1 * (fourierTransform μ f χ).re :=
            mul_le_mul_of_nonneg_right (ha01 χ).2 (hF0 χ)
        _ = (fourierTransform μ f χ).re := one_mul _
    linarith [hclaimA ▸ hle, hage]

/-- **The total mass identity**: `∫ 𝓕f ∂(dualHaar μ) = σ_f(Ĝ)`. -/
theorem integral_fourierTransform_dualHaar (hfi : Integrable f μ)
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf) :
    ∫ χ, fourierTransform μ f χ ∂(dualHaar μ) = ((σf.real Set.univ : ℝ) : ℂ) := by
  calc ∫ χ, fourierTransform μ f χ ∂(dualHaar μ)
      = ∫ χ, (((fourierTransform μ f χ).re : ℝ) : ℂ) ∂(dualHaar μ) :=
        integral_congr_ae (Eventually.of_forall fun χ =>
          fourierTransform_eq_ofReal_re μ σf hrep χ)
    _ = ((∫ χ, (fourierTransform μ f χ).re ∂(dualHaar μ) : ℝ) : ℂ) := integral_ofReal
    _ = ((σf.real Set.univ : ℝ) : ℂ) := by
        rw [integral_re_fourierTransform_dualHaar μ σf hfi hrep]

/-- **The tail bound**: outside a suitable compact set of characters, the transform has
arbitrarily small integral. -/
theorem exists_isCompact_setIntegral_re_fourierTransform_compl_le (hfi : Integrable f μ)
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Set (PontryaginDual G), IsCompact Q ∧
      ∫ χ in Qᶜ, (fourierTransform μ f χ).re ∂(dualHaar μ) ≤ ε := by
  obtain ⟨a, hac, has, ha01, hage⟩ := exists_cutoff_integral_ge σf hε
  refine ⟨tsupport a, has, ?_⟩
  have hFc : Continuous fun χ => (fourierTransform μ f χ).re :=
    Complex.continuous_re.comp (continuous_fourierTransform μ hfi)
  have hF0 : ∀ χ, 0 ≤ (fourierTransform μ f χ).re :=
    fourierTransform_re_nonneg μ σf hfi hrep
  have hFint := integrable_re_fourierTransform_dualHaar μ σf hfi hrep
  have haF_int : Integrable (fun χ => a χ * (fourierTransform μ f χ).re) (dualHaar μ) :=
    (hac.mul hFc).integrable_of_hasCompactSupport has.mul_right
  have hQmeas : MeasurableSet (tsupport a) := (isClosed_tsupport a).measurableSet
  have hsplit : (∫ χ in tsupport a, (fourierTransform μ f χ).re ∂(dualHaar μ))
      + ∫ χ in (tsupport a)ᶜ, (fourierTransform μ f χ).re ∂(dualHaar μ)
      = ∫ χ, (fourierTransform μ f χ).re ∂(dualHaar μ) :=
    integral_add_compl hQmeas hFint
  have h1 : ∫ χ, a χ * (fourierTransform μ f χ).re ∂(dualHaar μ)
      ≤ ∫ χ in tsupport a, (fourierTransform μ f χ).re ∂(dualHaar μ) := by
    have heq : ∫ χ, a χ * (fourierTransform μ f χ).re ∂(dualHaar μ)
        = ∫ χ in tsupport a, a χ * (fourierTransform μ f χ).re ∂(dualHaar μ) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun χ hχ => by rw [image_eq_zero_of_notMem_tsupport hχ, zero_mul])).symm
    rw [heq]
    refine setIntegral_mono_on haF_int.integrableOn hFint.integrableOn hQmeas
      fun χ _ => ?_
    calc a χ * (fourierTransform μ f χ).re
        ≤ 1 * (fourierTransform μ f χ).re :=
          mul_le_mul_of_nonneg_right (ha01 χ).2 (hF0 χ)
      _ = (fourierTransform μ f χ).re := one_mul _
  have h2 := integral_cc_mul_re_fourierTransform_dualHaar μ σf hfi hrep hac has
  have h3 := integral_re_fourierTransform_dualHaar μ σf hfi hrep
  linarith [h2 ▸ h1, hage, hsplit, h3]

/-- **The density identity for bounded continuous integrands**:
`∫ χ, v(χ) ⬝ 𝓕f(χ) ∂(dualHaar μ) = ∫ χ, v(χ) ∂σ_f` for every bounded continuous `v`. -/
theorem integral_bddContinuous_mul_fourierTransform_dualHaar (hfi : Integrable f μ)
    (hrep : ∀ x : G, f x = ∫ χ, (χ x : ℂ) ∂σf)
    {v : PontryaginDual G → ℂ} (hvc : Continuous v) {Cv : ℝ} (hvb : ∀ χ, ‖v χ‖ ≤ Cv) :
    ∫ χ, v χ * fourierTransform μ f χ ∂(dualHaar μ) = ∫ χ, v χ ∂σf := by
  have hCv0 : 0 ≤ Cv := (norm_nonneg (v 1)).trans (hvb 1)
  have hFc : Continuous fun χ => (fourierTransform μ f χ).re :=
    Complex.continuous_re.comp (continuous_fourierTransform μ hfi)
  have hF0 : ∀ χ, 0 ≤ (fourierTransform μ f χ).re :=
    fourierTransform_re_nonneg μ σf hfi hrep
  have hFnorm : ∀ χ, ‖fourierTransform μ f χ‖ = (fourierTransform μ f χ).re := fun χ => by
    conv_lhs => rw [fourierTransform_eq_ofReal_re μ σf hrep χ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF0 χ)]
  have hFint := integrable_re_fourierTransform_dualHaar μ σf hfi hrep
  have hI1 : Integrable (fun χ => v χ * fourierTransform μ f χ) (dualHaar μ) :=
    (integrable_fourierTransform_dualHaar μ σf hfi hrep).bdd_mul
      hvc.aestronglyMeasurable (Eventually.of_forall hvb)
  have hI3 : Integrable v σf :=
    (integrable_const Cv).mono' hvc.aestronglyMeasurable (Eventually.of_forall hvb)
  have hS := integral_re_fourierTransform_dualHaar μ σf hfi hrep
  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∫ χ, v χ * fourierTransform μ f χ ∂(dualHaar μ)) - ∫ χ, v χ ∂σf‖
        ≤ ε * (2 * Cv) := by
    intro ε hε
    obtain ⟨a, hac, has, ha01, hage⟩ := exists_cutoff_integral_ge σf hε
    have hclaimA := integral_cc_mul_re_fourierTransform_dualHaar μ σf hfi hrep hac has
    have haC : Continuous fun χ : PontryaginDual G => ((a χ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp hac
    have haCs : HasCompactSupport fun χ : PontryaginDual G => ((a χ : ℝ) : ℂ) :=
      has.comp_left (g := Complex.ofReal) Complex.ofReal_zero
    have haF_int : Integrable (fun χ => a χ * (fourierTransform μ f χ).re) (dualHaar μ) :=
      (hac.mul hFc).integrable_of_hasCompactSupport has.mul_right
    have haint : Integrable a σf := hac.integrable_of_hasCompactSupport has
    -- the middle identity for the `C_c` function `a ⬝ v`
    have hmid := integral_cc_mul_fourierTransform_dualHaar μ σf hfi hrep
      (a := fun χ => ((a χ : ℝ) : ℂ) * v χ) (haC.mul hvc) haCs.mul_right
    have hI2 : Integrable (fun χ => ((a χ : ℝ) : ℂ) * v χ * fourierTransform μ f χ)
        (dualHaar μ) :=
      ((haC.mul hvc).mul (continuous_fourierTransform μ hfi)).integrable_of_hasCompactSupport
        haCs.mul_right.mul_right
    have hI4 : Integrable (fun χ => ((a χ : ℝ) : ℂ) * v χ) σf := by
      refine (integrable_const Cv).mono' ((haC.mul hvc).aestronglyMeasurable)
        (Eventually.of_forall fun χ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha01 χ).1]
      calc a χ * ‖v χ‖ ≤ 1 * Cv :=
            mul_le_mul (ha01 χ).2 (hvb χ) (norm_nonneg _) zero_le_one
        _ = Cv := one_mul _
    -- the ν-side tail
    have htail1 : ‖(∫ χ, v χ * fourierTransform μ f χ ∂(dualHaar μ))
        - ∫ χ, ((a χ : ℝ) : ℂ) * v χ * fourierTransform μ f χ ∂(dualHaar μ)‖
        ≤ Cv * ε := by
      rw [← integral_sub hI1 hI2]
      have hdom : Integrable
          (fun χ => Cv * ((fourierTransform μ f χ).re
            - a χ * (fourierTransform μ f χ).re)) (dualHaar μ) :=
        (hFint.sub haF_int).const_mul Cv
      calc ‖∫ χ, (v χ * fourierTransform μ f χ
              - ((a χ : ℝ) : ℂ) * v χ * fourierTransform μ f χ) ∂(dualHaar μ)‖
          ≤ ∫ χ, Cv * ((fourierTransform μ f χ).re
              - a χ * (fourierTransform μ f χ).re) ∂(dualHaar μ) := by
            refine norm_integral_le_of_norm_le hdom (Eventually.of_forall fun χ => ?_)
            have hfactor : v χ * fourierTransform μ f χ
                - ((a χ : ℝ) : ℂ) * v χ * fourierTransform μ f χ
                = (1 - ((a χ : ℝ) : ℂ)) * (v χ * fourierTransform μ f χ) := by ring
            rw [hfactor, norm_mul, norm_mul, hFnorm χ]
            have h1a : ‖(1 : ℂ) - ((a χ : ℝ) : ℂ)‖ = 1 - a χ := by
              rw [show (1 : ℂ) - ((a χ : ℝ) : ℂ) = ((1 - a χ : ℝ) : ℂ) by push_cast; ring,
                Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [(ha01 χ).2])]
            rw [h1a]
            calc (1 - a χ) * (‖v χ‖ * (fourierTransform μ f χ).re)
                ≤ (1 - a χ) * (Cv * (fourierTransform μ f χ).re) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by linarith [(ha01 χ).2])
                  exact mul_le_mul_of_nonneg_right (hvb χ) (hF0 χ)
              _ = Cv * ((fourierTransform μ f χ).re - a χ * (fourierTransform μ f χ).re) := by
                  ring
        _ = Cv * ((∫ χ, (fourierTransform μ f χ).re ∂(dualHaar μ))
              - ∫ χ, a χ * (fourierTransform μ f χ).re ∂(dualHaar μ)) := by
            rw [← integral_sub hFint haF_int, ← integral_const_mul]
        _ ≤ Cv * ε := by
            refine mul_le_mul_of_nonneg_left ?_ hCv0
            rw [hS, hclaimA]
            linarith
    -- the σ_f-side tail
    have htail2 : ‖(∫ χ, ((a χ : ℝ) : ℂ) * v χ ∂σf) - ∫ χ, v χ ∂σf‖ ≤ Cv * ε := by
      rw [← integral_sub hI4 hI3]
      have hdom : Integrable (fun χ => Cv * (1 - a χ)) σf :=
        ((integrable_const (1 : ℝ)).sub haint).const_mul Cv
      calc ‖∫ χ, (((a χ : ℝ) : ℂ) * v χ - v χ) ∂σf‖
          ≤ ∫ χ, Cv * (1 - a χ) ∂σf := by
            refine norm_integral_le_of_norm_le hdom (Eventually.of_forall fun χ => ?_)
            have hfactor : ((a χ : ℝ) : ℂ) * v χ - v χ
                = -((1 - ((a χ : ℝ) : ℂ)) * v χ) := by ring
            rw [hfactor, norm_neg, norm_mul]
            have h1a : ‖(1 : ℂ) - ((a χ : ℝ) : ℂ)‖ = 1 - a χ := by
              rw [show (1 : ℂ) - ((a χ : ℝ) : ℂ) = ((1 - a χ : ℝ) : ℂ) by push_cast; ring,
                Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [(ha01 χ).2])]
            rw [h1a, mul_comm]
            exact mul_le_mul_of_nonneg_right (hvb χ) (by linarith [(ha01 χ).2])
        _ = Cv * ((σf.real Set.univ) - ∫ χ, a χ ∂σf) := by
            have h5 : ∫ χ, Cv * (1 - a χ) ∂σf = Cv * ∫ χ, (1 - a χ) ∂σf :=
              integral_const_mul _ _
            have h6 : ∫ χ, (1 - a χ) ∂σf = (σf.real Set.univ) - ∫ χ, a χ ∂σf := by
              rw [integral_sub (integrable_const 1) haint, integral_const, smul_eq_mul,
                mul_one]
            rw [h5, h6]
        _ ≤ Cv * ε := by
            refine mul_le_mul_of_nonneg_left ?_ hCv0
            linarith
    calc ‖(∫ χ, v χ * fourierTransform μ f χ ∂(dualHaar μ)) - ∫ χ, v χ ∂σf‖
        = ‖((∫ χ, v χ * fourierTransform μ f χ ∂(dualHaar μ))
              - ∫ χ, ((a χ : ℝ) : ℂ) * v χ * fourierTransform μ f χ ∂(dualHaar μ))
            + ((∫ χ, ((a χ : ℝ) : ℂ) * v χ ∂σf) - ∫ χ, v χ ∂σf)‖ := by
          rw [← hmid]
          congr 1
          ring
      _ ≤ ‖(∫ χ, v χ * fourierTransform μ f χ ∂(dualHaar μ))
              - ∫ χ, ((a χ : ℝ) : ℂ) * v χ * fourierTransform μ f χ ∂(dualHaar μ)‖
            + ‖(∫ χ, ((a χ : ℝ) : ℂ) * v χ ∂σf) - ∫ χ, v χ ∂σf‖ := norm_add_le _ _
      _ ≤ Cv * ε + Cv * ε := add_le_add htail1 htail2
      _ = ε * (2 * Cv) := by ring
  have h0 : ‖(∫ χ, v χ * fourierTransform μ f χ ∂(dualHaar μ)) - ∫ χ, v χ ∂σf‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hδ : 0 < ε / (2 * Cv + 1) := by positivity
    refine (key _ hδ).trans ?_
    have h3 : ε / (2 * Cv + 1) * (2 * Cv) ≤ ε / (2 * Cv + 1) * (2 * Cv + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ.le
    rw [div_mul_cancel₀ ε (by positivity : (2 * Cv + 1 : ℝ) ≠ 0)] at h3
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

end TransformIntegrable

/-! ### Fourier inversion -/

section Inversion

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- **Fourier inversion for positive-type functions.**  For a continuous integrable function
of positive type on a locally compact Hausdorff abelian group,

`f x = ∫ χ, χ(x) ⬝ 𝓕f(χ) ∂(dualHaar μ)`. -/
theorem IsPositiveType.fourier_inversion {f : G → ℂ} (hf : IsPositiveType f)
    (hfc : Continuous f) (hfi : Integrable f μ) (x : G) :
    f x = ∫ χ, (χ x : ℂ) * fourierTransform μ f χ ∂(dualHaar μ) := by
  obtain ⟨σf, hfin, hreg, hrep⟩ := hf.exists_bochner_measure μ hfc
  haveI := hfin
  haveI := hreg
  have h := integral_bddContinuous_mul_fourierTransform_dualHaar μ σf hfi hrep
    (v := fun χ : PontryaginDual G => ((χ x : Circle) : ℂ)) (continuous_char_apply x)
    (Cv := 1) (fun χ => by rw [Circle.norm_coe])
  rw [h]
  exact hrep x

/-- Fourier inversion at the identity: `f 1 = ∫ χ, 𝓕f(χ) ∂(dualHaar μ)`. -/
theorem IsPositiveType.fourier_inversion_one {f : G → ℂ} (hf : IsPositiveType f)
    (hfc : Continuous f) (hfi : Integrable f μ) :
    f 1 = ∫ χ, fourierTransform μ f χ ∂(dualHaar μ) := by
  rw [hf.fourier_inversion μ hfc hfi 1]
  refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
  show ((χ (1 : G) : Circle) : ℂ) * fourierTransform μ f χ = fourierTransform μ f χ
  rw [map_one, Circle.coe_one, one_mul]

end Inversion

/-! ### Normalized positive-type functions with small support -/

section Exports

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

include μ in
/-- **Normalized positive-type `C_c` functions with small support**: for every neighborhood
`U` of `1` in `G` there is a continuous compactly supported function of positive type with
`tsupport f ⊆ U` and `f 1 = 1` (a normalized convolution square of a bump). -/
theorem exists_positiveType_cc_eq_one (U : Set G) (hU : U ∈ nhds (1 : G)) :
    ∃ f : G → ℂ, IsPositiveType f ∧ Continuous f ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ f 1 = 1 := by
  -- a symmetric-ish neighborhood `V'` with `V' * V'⁻¹ ⊆ U`
  obtain ⟨V, hVopen, hV1, hVsub⟩ := exists_open_nhds_one_mul_subset hU
  set V' : Set G := V ∩ V⁻¹ with hV'def
  have hV'nhds : V' ∈ nhds (1 : G) :=
    Filter.inter_mem (hVopen.mem_nhds hV1)
      (inv_mem_nhds_one G (hVopen.mem_nhds hV1))
  obtain ⟨h, hhc, hhs, hh0, hhsupp, hhint⟩ := exists_normalized_bump μ V' hV'nhds
  set hC : G → ℂ := fun x => ((h x : ℝ) : ℂ) with hhCdef
  have hhCc : Continuous hC := Complex.continuous_ofReal.comp hhc
  have hhCs : HasCompactSupport hC := hhs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hhCsupp : tsupport hC ⊆ V' := by
    refine subset_trans (closure_mono fun x hx => ?_) hhsupp
    simp only [mem_support] at hx ⊢
    exact fun h0 => hx (by rw [hhCdef]; simp [h0])
  set e : G → ℂ := mconv μ hC (mstar hC) with hedef
  have hec : Continuous e := hhCc.mconv μ hhCs hhCc.mstar hhCs.mstar
  have hes : HasCompactSupport e := hhCs.mconv μ hhCs.mstar
  have hpt : IsPositiveType e := isPositiveType_mconv_mstar μ hhCc hhCs
  -- support control
  have hesupp : tsupport e ⊆ U := by
    calc tsupport e ⊆ tsupport hC * tsupport (mstar hC) :=
          tsupport_mconv_subset μ hhCs hhCs.mstar
      _ = tsupport hC * (tsupport hC)⁻¹ := by rw [tsupport_mstar]
      _ ⊆ V' * V'⁻¹ := Set.mul_subset_mul hhCsupp (Set.inv_subset_inv.mpr hhCsupp)
      _ ⊆ V * V := by
          refine Set.mul_subset_mul (Set.inter_subset_left) ?_
          rw [hV'def, Set.inter_inv, inv_inv]
          exact Set.inter_subset_right
      _ ⊆ U := hVsub
  -- normalization
  have he1 : e 1 = ((∫ y, ‖hC y‖ ^ 2 ∂μ : ℝ) : ℂ) := mconv_mstar_self_one μ hC
  have hr : 0 < ∫ y, ‖hC y‖ ^ 2 ∂μ := by
    have hsqeq : (fun y => ‖hC y‖ ^ 2) = fun y => h y ^ 2 := funext fun y => by
      show ‖((h y : ℝ) : ℂ)‖ ^ 2 = h y ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hsqeq]
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, h x₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [show h = fun _ => (0 : ℝ) from funext hcon] at hhint
      simp at hhint
    have hsqc : Continuous fun y => h y ^ 2 := by fun_prop
    have hsqs : HasCompactSupport fun y => h y ^ 2 := by
      refine hhs.mono fun y hy => ?_
      simp only [mem_support] at hy ⊢
      exact fun h0 => hy (by rw [h0]; ring)
    exact integral_pos_of_integrable_nonneg_nonzero (x := x₀) hsqc
      (hsqc.integrable_of_hasCompactSupport hsqs) (fun y => sq_nonneg _)
      (pow_ne_zero 2 hx₀)
  set r : ℝ := ∫ y, ‖hC y‖ ^ 2 ∂μ with hrdef
  refine ⟨r⁻¹ • e, hpt.smul_of_nonneg (inv_nonneg.mpr hr.le), hec.const_smul r⁻¹,
    hes.mono (support_const_smul_subset r⁻¹ e), ?_, ?_⟩
  · exact subset_trans (closure_mono (support_const_smul_subset r⁻¹ e)) hesupp
  · show r⁻¹ • e 1 = 1
    rw [he1, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne',
      Complex.ofReal_one]

end Exports

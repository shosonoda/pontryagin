/-
Copyright (c) 2026 The pontryagin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The pontryagin contributors
-/
import Pontryagin.L1Algebra
import Pontryagin.FourierTransform
import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Gelfand spectrum of the convolution algebra `L¹(G)`

For a locally compact Hausdorff abelian group `G` with regular Haar measure `μ`, this file
identifies the characters of the commutative Banach algebra `L1G μ` (convolution on `L¹`)
with the points of the Pontryagin dual, via the Fourier transform.

## Main definitions

* `L1G.fourier μ F`: the Fourier transform of an `L¹` class, a function on the dual group;
* `L1G.fourierC0 μ F`: the same, bundled in `C₀(PontryaginDual G, ℂ)` (continuity plus the
  Riemann–Lebesgue lemma);
* `L1G.fourierHom μ : L1G μ →⋆ₙₐ[ℂ] C₀(PontryaginDual G, ℂ)`: the Fourier transform as a
  homomorphism of non-unital star algebras;
* `L1G.translate μ a F`: left translation on `L1G μ`;
* `pairCLM μ h`: testing an `L¹` class against a continuous compactly supported function,
  as a continuous linear functional.

## Main results

* `L1G.fourier_mul`, `L1G.fourier_star`, `L1G.norm_fourier_apply_le`,
  `L1G.norm_fourierC0_le`: the algebraic and metric properties of the transform, obtained
  from the `C_c` identities of `Pontryagin.FourierTransform` by density;
* `toLpCc_mconv_eq_integral`: the Bochner-integral form of convolution,
  `class (f ⋆ g) = ∫ a, f a • Lₐ (class g) ∂μ`;
* `fourierTransform_separates`: distinct characters are separated by the Fourier transforms
  of `C_c` functions;
* `exists_fourierTransform_eq_one`: the Fourier transform does not vanish identically at any
  character (a normalized bump times the character transforms to `1`);
* `L1G.characterSpace_exists_char`: **every character of `L¹(G)` is given by a unique
  point of the Pontryagin dual**, `φ F = 𝓕F(χ)` — the translation-ratio argument.
-/

noncomputable section

open Filter Function MeasureTheory Set Topology WeakDual WeakDual.CharacterSpace PontryaginDual
open scoped ComplexConjugate ENNReal ZeroAtInfty

-- The sections below deliberately use one coarse hypothesis block (locally compact Hausdorff
-- abelian group with regular Haar measure) rather than minimal per-lemma assumptions.
set_option linter.unusedSectionVars false

-- `show` is used pervasively to cross the definitional equality between the type synonym
-- `L1G μ` and `Lp ℂ 1 μ`, and to beta-reduce integrands.
set_option linter.style.show false

namespace MeasureTheory

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-! ### The Fourier transform on `L¹` classes -/

section FourierLp

/-- On a `C_c` class the Fourier transform is computed by the representative. -/
theorem fourierTransform_coeFn_toLpCc (f : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) :
    fourierTransform μ ⇑(toLpCc μ f hfc hfs) = fourierTransform μ f :=
  fourierTransform_congr_ae (coeFn_toLpCc μ f hfc hfs)

/-- The Fourier transform at a fixed character is `1`-Lipschitz on `L¹`. -/
theorem norm_fourierTransform_coeFn_sub_le (F K : Lp ℂ 1 μ) (χ : PontryaginDual G) :
    ‖fourierTransform μ ⇑F χ - fourierTransform μ ⇑K χ‖ ≤ ‖F - K‖ :=
  (norm_fourierTransform_sub_le μ (L1.integrable_coeFn F) (L1.integrable_coeFn K) χ).trans
    (le_of_eq (norm_sub_eq_integral μ F K).symm)

/-- The Fourier transform at a fixed character is a continuous function of the `L¹` class. -/
theorem continuous_fourierTransform_coeFn (χ : PontryaginDual G) :
    Continuous fun F : Lp ℂ 1 μ => fourierTransform μ ⇑F χ :=
  (LipschitzWith.of_dist_le_mul fun F K => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact norm_fourierTransform_coeFn_sub_le μ F K χ).continuous

namespace L1G

/-- The Fourier transform of an element of the convolution algebra `L1G μ`. -/
def fourier (F : L1G μ) : PontryaginDual G → ℂ :=
  fourierTransform μ ⇑(toLp μ F)

theorem fourier_def (F : L1G μ) (χ : PontryaginDual G) :
    fourier μ F χ = ∫ x, (toLp μ F : Lp ℂ 1 μ) x * conj (χ x : ℂ) ∂μ := rfl

/-- The Fourier transform of a `C_c` class is the Fourier transform of the representative. -/
theorem fourier_ofLp_toLpCc (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    fourier μ (ofLp μ (toLpCc μ f hfc hfs)) = fourierTransform μ f :=
  fourierTransform_coeFn_toLpCc μ f hfc hfs

/-- The trivial bound: the transform is dominated by the `L¹` norm. -/
theorem norm_fourier_apply_le (F : L1G μ) (χ : PontryaginDual G) :
    ‖fourier μ F χ‖ ≤ ‖F‖ :=
  (norm_fourierTransform_le μ _ χ).trans
    (le_of_eq ((L1.norm_eq_integral_norm (toLp μ F)).symm.trans (norm_toLp μ F)))

theorem fourier_add (F K : L1G μ) (χ : PontryaginDual G) :
    fourier μ (F + K) χ = fourier μ F χ + fourier μ K χ := by
  show fourierTransform μ ⇑(toLp μ F + toLp μ K) χ = _
  rw [fourierTransform_congr_ae (Lp.coeFn_add (toLp μ F) (toLp μ K)),
    fourierTransform_add μ (L1.integrable_coeFn _) (L1.integrable_coeFn _)]
  rfl

theorem fourier_smul (c : ℂ) (F : L1G μ) (χ : PontryaginDual G) :
    fourier μ (c • F) χ = c * fourier μ F χ := by
  show fourierTransform μ ⇑(c • toLp μ F) χ = _
  rw [fourierTransform_congr_ae (Lp.coeFn_smul c (toLp μ F)), fourierTransform_smul μ c]
  rfl

theorem fourier_zero (χ : PontryaginDual G) : fourier μ (0 : L1G μ) χ = 0 := by
  show fourierTransform μ ⇑(0 : Lp ℂ 1 μ) χ = 0
  rw [fourierTransform_congr_ae (Lp.coeFn_zero ℂ 1 μ), fourierTransform_apply]
  simp

/-- **Multiplicativity of the Fourier transform** on `L¹`, by density from
`fourierTransform_mconv`. -/
theorem fourier_mul (F K : L1G μ) (χ : PontryaginDual G) :
    fourier μ (F * K) χ = fourier μ F χ * fourier μ K χ := by
  have key : ∀ Fp Kp : Lp ℂ 1 μ,
      fourierTransform μ ⇑(mulCLM μ Fp Kp) χ
        = fourierTransform μ ⇑Fp χ * fourierTransform μ ⇑Kp χ := by
    have step1 : ∀ (g : G → ℂ) (hgc : Continuous g) (hgs : HasCompactSupport g)
        (Fp : Lp ℂ 1 μ),
        fourierTransform μ ⇑(mulCLM μ Fp (toLpCc μ g hgc hgs)) χ
          = fourierTransform μ ⇑Fp χ * fourierTransform μ ⇑(toLpCc μ g hgc hgs) χ := by
      intro g hgc hgs
      refine funext_of_dense μ
        (fun Fp => fourierTransform μ ⇑(mulCLM μ Fp (toLpCc μ g hgc hgs)) χ)
        (fun Fp => fourierTransform μ ⇑Fp χ * fourierTransform μ ⇑(toLpCc μ g hgc hgs) χ)
        ((continuous_fourierTransform_coeFn μ χ).comp
          ((mulCLM μ).flip (toLpCc μ g hgc hgs)).continuous)
        ((continuous_fourierTransform_coeFn μ χ).mul continuous_const) ?_
      intro f hfc hfs
      rw [mulCLM_toLpCc μ f g hfc hfs hgc hgs,
        fourierTransform_coeFn_toLpCc μ (mconv μ f g) _ _,
        fourierTransform_coeFn_toLpCc μ f hfc hfs,
        fourierTransform_coeFn_toLpCc μ g hgc hgs,
        fourierTransform_mconv μ hfc hfs hgc hgs χ]
    intro Fp Kp
    refine funext_of_dense μ
      (fun Kp => fourierTransform μ ⇑(mulCLM μ Fp Kp) χ)
      (fun Kp => fourierTransform μ ⇑Fp χ * fourierTransform μ ⇑Kp χ)
      ((continuous_fourierTransform_coeFn μ χ).comp (mulCLM μ Fp).continuous)
      (continuous_const.mul (continuous_fourierTransform_coeFn μ χ)) ?_ Kp
    intro g hgc hgs
    exact step1 g hgc hgs Fp
  exact key (toLp μ F) (toLp μ K)

/-- The Fourier transform intertwines the star involution and complex conjugation. -/
theorem fourier_star (F : L1G μ) (χ : PontryaginDual G) :
    fourier μ (star F) χ = conj (fourier μ F χ) := by
  show fourierTransform μ ⇑(L1star μ (toLp μ F)) χ = _
  rw [fourierTransform_congr_ae (coeFn_L1star μ (toLp μ F)),
    fourierTransform_mstar μ ⇑(toLp μ F) χ]
  rfl

theorem fourier_continuous (F : L1G μ) : Continuous (fourier μ F) :=
  continuous_fourierTransform μ (L1.integrable_coeFn (toLp μ F))

theorem fourier_zeroAtInfty (F : L1G μ) :
    Tendsto (fourier μ F) (cocompact (PontryaginDual G)) (nhds 0) :=
  tendsto_fourierTransform_cocompact μ (L1.integrable_coeFn (toLp μ F))

/-- The Fourier transform of an `L¹` class, as an element of `C₀(Ĝ, ℂ)`. -/
def fourierC0 (F : L1G μ) : C₀(PontryaginDual G, ℂ) where
  toFun := fourier μ F
  continuous_toFun := fourier_continuous μ F
  zero_at_infty' := fourier_zeroAtInfty μ F

@[simp]
theorem coe_fourierC0 (F : L1G μ) : ⇑(fourierC0 μ F) = fourier μ F := rfl

/-- The sup-norm of the bundled Fourier transform is at most the `L¹` norm. -/
theorem norm_fourierC0_le (F : L1G μ) : ‖fourierC0 μ F‖ ≤ ‖F‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
    fun χ => norm_fourier_apply_le μ F χ

/-- **The Fourier transform as a homomorphism of non-unital star algebras**
`L¹(G) →⋆ₙₐ[ℂ] C₀(Ĝ, ℂ)`. -/
def fourierHom : L1G μ →⋆ₙₐ[ℂ] C₀(PontryaginDual G, ℂ) where
  toFun := fourierC0 μ
  map_smul' c F := by
    ext χ
    rw [ZeroAtInftyContinuousMap.smul_apply]
    exact fourier_smul μ c F χ
  map_zero' := by
    ext χ
    rw [ZeroAtInftyContinuousMap.zero_apply]
    exact fourier_zero μ χ
  map_add' F K := by
    ext χ
    rw [ZeroAtInftyContinuousMap.add_apply]
    exact fourier_add μ F K χ
  map_mul' F K := by
    ext χ
    rw [ZeroAtInftyContinuousMap.mul_apply]
    exact fourier_mul μ F K χ
  map_star' F := by
    ext χ
    rw [ZeroAtInftyContinuousMap.star_apply]
    exact fourier_star μ F χ

@[simp]
theorem fourierHom_apply (F : L1G μ) : fourierHom μ F = fourierC0 μ F := rfl

end L1G

end FourierLp

/-! ### Translation on `L1G` -/

section TranslateL1

/-- Translation of a `C_c` class is the class of the translated representative. -/
theorem translateLp_toLpCc (a : G) (f : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) :
    translateLp μ 1 a (toLpCc μ f hfc hfs)
      = toLpCc μ (mtranslate a f) (hfc.mtranslate a) (hfs.mtranslate a) := by
  refine Lp.ext ?_
  have h2 : mtranslate a ⇑(toLpCc μ f hfc hfs) =ᵐ[μ] mtranslate a f :=
    (measurePreserving_mul_left μ a⁻¹).quasiMeasurePreserving.ae_eq_comp
      (coeFn_toLpCc μ f hfc hfs)
  exact ((coeFn_translateLp μ 1 a _).trans h2).trans (coeFn_toLpCc μ _ _ _).symm

/-- Translation commutes with convolution in the first slot, by density from
`mtranslate_mconv`. -/
theorem translateLp_mulCLM (a : G) (F K : Lp ℂ 1 μ) :
    translateLp μ 1 a (mulCLM μ F K) = mulCLM μ (translateLp μ 1 a F) K := by
  have step1 : ∀ (g : G → ℂ) (hgc : Continuous g) (hgs : HasCompactSupport g)
      (F : Lp ℂ 1 μ),
      translateLp μ 1 a (mulCLM μ F (toLpCc μ g hgc hgs))
        = mulCLM μ (translateLp μ 1 a F) (toLpCc μ g hgc hgs) := by
    intro g hgc hgs
    refine funext_of_dense μ
      (fun F => translateLp μ 1 a (mulCLM μ F (toLpCc μ g hgc hgs)))
      (fun F => mulCLM μ (translateLp μ 1 a F) (toLpCc μ g hgc hgs))
      ((translateLp μ 1 a).continuous.comp
        ((mulCLM μ).flip (toLpCc μ g hgc hgs)).continuous)
      (((mulCLM μ).flip (toLpCc μ g hgc hgs)).continuous.comp
        (translateLp μ 1 a).continuous) ?_
    intro f hfc hfs
    rw [mulCLM_toLpCc μ f g hfc hfs hgc hgs,
      translateLp_toLpCc μ a (mconv μ f g) _ _, translateLp_toLpCc μ a f hfc hfs,
      mulCLM_toLpCc μ (mtranslate a f) g _ _ hgc hgs]
    exact toLpCc_congr μ _ _ _ _ (mtranslate_mconv μ a f g)
  refine funext_of_dense μ
    (fun K => translateLp μ 1 a (mulCLM μ F K))
    (fun K => mulCLM μ (translateLp μ 1 a F) K)
    ((translateLp μ 1 a).continuous.comp (mulCLM μ F).continuous)
    ((mulCLM μ (translateLp μ 1 a F)).continuous) ?_ K
  intro g hgc hgs
  exact step1 g hgc hgs F

namespace L1G

/-- Left translation on the convolution algebra `L1G μ`. -/
def translate (a : G) (F : L1G μ) : L1G μ :=
  ofLp μ (translateLp μ 1 a (toLp μ F))

@[simp]
theorem toLp_translate (a : G) (F : L1G μ) :
    toLp μ (translate μ a F) = translateLp μ 1 a (toLp μ F) := rfl

@[simp]
theorem norm_translate (a : G) (F : L1G μ) : ‖translate μ a F‖ = ‖F‖ :=
  norm_translateLp μ 1 a (toLp μ F)

@[simp]
theorem translate_one (F : L1G μ) : translate μ 1 F = F :=
  congrArg (ofLp μ) (translateLp_one μ 1 (toLp μ F))

theorem translate_translate (a b : G) (F : L1G μ) :
    translate μ a (translate μ b F) = translate μ (a * b) F :=
  (congrArg (ofLp μ) (translateLp_mul μ 1 a b (toLp μ F))).symm

theorem continuous_translate (F : L1G μ) : Continuous fun a : G => translate μ a F :=
  continuous_translateLp μ 1 ENNReal.one_ne_top (toLp μ F)

/-- Translation commutes with multiplication in `L1G μ`. -/
theorem translate_mul (a : G) (F K : L1G μ) :
    translate μ a (F * K) = translate μ a F * K :=
  congrArg (ofLp μ) (translateLp_mulCLM μ a (toLp μ F) (toLp μ K))

end L1G

end TranslateL1

/-! ### The Bochner-integral form of convolution -/

section VectorConvolution

/-- The vector-valued integrand `a ↦ f a • Lₐ K` is integrable for `f` continuous compactly
supported. -/
theorem integrable_smul_translateLp (f : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (K : Lp ℂ 1 μ) :
    Integrable (fun a => f a • translateLp μ 1 a K) μ := by
  have hc : Continuous fun a => f a • translateLp μ 1 a K :=
    hfc.smul (continuous_translateLp μ 1 ENNReal.one_ne_top K)
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact hfs
    fun a ha => subset_tsupport f ?_
  simp only [mem_support] at ha ⊢
  intro hfa
  exact ha (by rw [hfa, zero_smul])

/-- The product of the coeFn of an `L¹` class with a `C_c` function is integrable. -/
theorem integrable_coeFn_mul_of_cc (u : Lp ℂ 1 μ) {h : G → ℂ} (hhc : Continuous h)
    (hhs : HasCompactSupport h) : Integrable (fun x => u x * h x) μ := by
  obtain ⟨C, hC⟩ := hhc.bounded_above_of_compact_support hhs
  exact (L1.integrable_coeFn u).mul_bdd hhc.aestronglyMeasurable (Eventually.of_forall hC)

/-- Testing an `L¹` class against a continuous compactly supported function, as a continuous
linear functional. -/
def pairCLM (h : G → ℂ) (hhc : Continuous h) (hhs : HasCompactSupport h) :
    Lp ℂ 1 μ →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun u : Lp ℂ 1 μ => ∫ x, u x * h x ∂μ
      map_add' := fun u v => by
        rw [← integral_add (integrable_coeFn_mul_of_cc μ u hhc hhs)
          (integrable_coeFn_mul_of_cc μ v hhc hhs)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add u v] with x hx
        rw [hx, Pi.add_apply, add_mul]
      map_smul' := fun c u => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c u] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc] }
    (by
      obtain ⟨C, hC⟩ := hhc.bounded_above_of_compact_support hhs
      refine ⟨C, fun u => ?_⟩
      calc ‖∫ x, u x * h x ∂μ‖
          ≤ ∫ x, ‖u x‖ * C ∂μ := by
            refine norm_integral_le_of_norm_le
              (((L1.integrable_coeFn u).norm).mul_const C)
              (Eventually.of_forall fun x => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
        _ = C * ‖u‖ := by
            rw [integral_mul_const, ← L1.norm_eq_integral_norm, mul_comm])

@[simp]
theorem pairCLM_apply (h : G → ℂ) (hhc : Continuous h) (hhs : HasCompactSupport h)
    (u : Lp ℂ 1 μ) : pairCLM μ h hhc hhs u = ∫ x, u x * h x ∂μ := rfl

/-- **The Bochner-integral form of convolution**: for continuous compactly supported `f`, `g`,
the `L¹` class of `f ⋆ g` is the vector integral `∫ a, f a • Lₐ (class g) ∂μ`. -/
theorem toLpCc_mconv_eq_integral (f g : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (hgc : Continuous g) (hgs : HasCompactSupport g) :
    toLpCc μ (mconv μ f g) (hfc.mconv μ hfs hgc hgs) (hfs.mconv μ hgs)
      = ∫ a, f a • translateLp μ 1 a (toLpCc μ g hgc hgs) ∂μ := by
  have hΦi : Integrable (fun a => f a • translateLp μ 1 a (toLpCc μ g hgc hgs)) μ :=
    integrable_smul_translateLp μ f hfc hfs _
  -- the pointwise description of the integrand
  have hΦcoe : ∀ a : G,
      ⇑(f a • translateLp μ 1 a (toLpCc μ g hgc hgs)) =ᵐ[μ] fun x => f a * g (a⁻¹ * x) := by
    intro a
    rw [translateLp_toLpCc μ a g hgc hgs]
    filter_upwards [Lp.coeFn_smul (f a)
        (toLpCc μ (mtranslate a g) (hgc.mtranslate a) (hgs.mtranslate a)),
      coeFn_toLpCc μ (mtranslate a g) (hgc.mtranslate a) (hgs.mtranslate a)] with x hx1 hx2
    rw [hx1, Pi.smul_apply, hx2]
    simp [mtranslate_apply, smul_eq_mul]
  rw [← sub_eq_zero]
  -- test the difference against arbitrary C_c functions
  have htest : ∀ h : G → ℂ, Continuous h → HasCompactSupport h →
      ∫ x, (toLpCc μ (mconv μ f g) (hfc.mconv μ hfs hgc hgs) (hfs.mconv μ hgs)
        - ∫ a, f a • translateLp μ 1 a (toLpCc μ g hgc hgs) ∂μ : Lp ℂ 1 μ) x * h x ∂μ = 0 := by
    intro h hhc hhs
    have hDpair : ∫ x, (toLpCc μ (mconv μ f g) (hfc.mconv μ hfs hgc hgs) (hfs.mconv μ hgs)
          - ∫ a, f a • translateLp μ 1 a (toLpCc μ g hgc hgs) ∂μ : Lp ℂ 1 μ) x * h x ∂μ
        = pairCLM μ h hhc hhs
            (toLpCc μ (mconv μ f g) (hfc.mconv μ hfs hgc hgs) (hfs.mconv μ hgs))
          - pairCLM μ h hhc hhs (∫ a, f a • translateLp μ 1 a (toLpCc μ g hgc hgs) ∂μ) := by
      rw [← map_sub]
      rfl
    -- the left pairing is the double integral in one order
    have hL : pairCLM μ h hhc hhs
        (toLpCc μ (mconv μ f g) (hfc.mconv μ hfs hgc hgs) (hfs.mconv μ hgs))
        = ∫ x, mconv μ f g x * h x ∂μ := by
      rw [pairCLM_apply]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_toLpCc μ (mconv μ f g) (hfc.mconv μ hfs hgc hgs)
        (hfs.mconv μ hgs)] with x hx
      rw [hx]
    -- the right pairing is the double integral in the other order
    have hR : pairCLM μ h hhc hhs (∫ a, f a • translateLp μ 1 a (toLpCc μ g hgc hgs) ∂μ)
        = ∫ a, ∫ x, f a * g (a⁻¹ * x) * h x ∂μ ∂μ := by
      rw [← ContinuousLinearMap.integral_comp_comm (pairCLM μ h hhc hhs) hΦi]
      refine integral_congr_ae (Eventually.of_forall fun a => ?_)
      show pairCLM μ h hhc hhs (f a • translateLp μ 1 a (toLpCc μ g hgc hgs))
          = ∫ x, f a * g (a⁻¹ * x) * h x ∂μ
      rw [pairCLM_apply]
      refine integral_congr_ae ?_
      filter_upwards [hΦcoe a] with x hx
      rw [hx]
    -- Fubini for the jointly continuous compactly supported kernel
    have hkc : Continuous (uncurry fun x a : G => f a * g (a⁻¹ * x) * h x) :=
      (mconv_kernel_continuous hfc hgc).mul (hhc.comp continuous_fst)
    have hks : HasCompactSupport (uncurry fun x a : G => f a * g (a⁻¹ * x) * h x) := by
      refine HasCompactSupport.of_support_subset_isCompact
        ((hfs.isCompact.mul hgs.isCompact).prod hfs.isCompact) fun p hp => ?_
      have hp' : f p.2 * g (p.2⁻¹ * p.1) ≠ 0 := left_ne_zero_of_mul hp
      exact mconv_kernel_support_subset hp'
    have hswap : ∫ x, mconv μ f g x * h x ∂μ
        = ∫ a, ∫ x, f a * g (a⁻¹ * x) * h x ∂μ ∂μ :=
      calc ∫ x, mconv μ f g x * h x ∂μ
          = ∫ x, ∫ a, f a * g (a⁻¹ * x) * h x ∂μ ∂μ := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_)
            exact (integral_mul_const _ _).symm
        _ = ∫ a, ∫ x, f a * g (a⁻¹ * x) * h x ∂μ ∂μ :=
            integral_integral_swap_of_hasCompactSupport hkc hks
    rw [hDpair, hL, hR, hswap, sub_self]
  have hae : ⇑(toLpCc μ (mconv μ f g) (hfc.mconv μ hfs hgc hgs) (hfs.mconv μ hgs)
      - ∫ a, f a • translateLp μ 1 a (toLpCc μ g hgc hgs) ∂μ : Lp ℂ 1 μ) =ᵐ[μ] 0 :=
    ae_eq_zero_of_forall_integral_mul_eq_zero (L1.integrable_coeFn _) htest
  exact Lp.ext (hae.trans (Lp.coeFn_zero ℂ 1 μ).symm)

end VectorConvolution

/-! ### Separation and non-vanishing of `C_c` transforms -/

section Separation

/-- **Fourier transforms of `C_c` functions separate characters.** -/
theorem _root_.PontryaginDual.fourierTransform_separates {χ χ' : PontryaginDual G} (hne : χ ≠ χ') :
    ∃ f : G → ℂ, Continuous f ∧ HasCompactSupport f ∧
      fourierTransform μ f χ ≠ fourierTransform μ f χ' := by
  -- a point where the characters differ, and the difference of conjugates
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, χ x₀ ≠ χ' x₀ := by
    by_contra hcon
    push Not at hcon
    exact hne (PontryaginDual.ext hcon)
  have hucont : Continuous fun x : G => conj (χ x : ℂ) - conj ((χ' x : Circle) : ℂ) :=
    (Complex.continuous_conj.comp (continuous_induced_dom.comp (map_continuous χ))).sub
      (Complex.continuous_conj.comp (continuous_induced_dom.comp (map_continuous χ')))
  have hu0 : conj (χ x₀ : ℂ) - conj ((χ' x₀ : Circle) : ℂ) ≠ 0 := by
    refine sub_ne_zero.mpr fun heq => hx₀ (Circle.coe_injective ?_)
    have h1 := congrArg (starRingEnd ℂ) heq
    simpa using h1
  set u : G → ℂ := fun x => conj (χ x : ℂ) - conj ((χ' x : Circle) : ℂ) with hu
  have hpos : 0 < ‖u x₀‖ := norm_pos_iff.mpr hu0
  -- a neighborhood of `x₀` where `u` is within `‖u x₀‖ / 2` of `u x₀`
  have hV : {x : G | ‖u x - u x₀‖ < ‖u x₀‖ / 2} ∈ nhds x₀ := by
    have hc : Continuous fun x => ‖u x - u x₀‖ := (hucont.sub continuous_const).norm
    have h0 : Set.Iio (‖u x₀‖ / 2) ∈ nhds ((fun x => ‖u x - u x₀‖) x₀) := by
      simpa using Iio_mem_nhds (half_pos hpos)
    exact hc.continuousAt.preimage_mem_nhds h0
  -- a normalized bump at `x₀`
  have hU : (fun y : G => x₀ * y) ⁻¹' {x : G | ‖u x - u x₀‖ < ‖u x₀‖ / 2}
      ∈ nhds (1 : G) := by
    refine ((continuous_const.mul continuous_id).continuousAt
      (x := (1 : G))).preimage_mem_nhds ?_
    simpa using hV
  obtain ⟨h₀, hh₀c, hh₀s, hh₀0, hh₀supp, hh₀int⟩ := exists_normalized_bump μ _ hU
  have hψc : Continuous (mtranslate x₀ h₀) := hh₀c.mtranslate x₀
  have hψs : HasCompactSupport (mtranslate x₀ h₀) := hh₀s.mtranslate x₀
  have hψ0 : ∀ x, 0 ≤ mtranslate x₀ h₀ x := fun x => hh₀0 _
  have hψint : ∫ x, mtranslate x₀ h₀ x ∂μ = 1 := by
    rw [integral_mtranslate μ x₀ h₀]
    exact hh₀int
  have hψsupp : tsupport (mtranslate x₀ h₀) ⊆ {x : G | ‖u x - u x₀‖ < ‖u x₀‖ / 2} := by
    rw [tsupport_mtranslate x₀ h₀]
    rintro z ⟨y, hy, rfl⟩
    simpa [smul_eq_mul] using hh₀supp hy
  -- the complex bump
  have hψcc : Continuous fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hψc
  have hψcs : HasCompactSupport fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ) :=
    hψs.comp_left Complex.ofReal_zero
  have hψci : Integrable (fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ)) μ :=
    hψcc.integrable_of_hasCompactSupport hψcs
  have hψcint : ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) ∂μ = 1 := by
    rw [show ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) ∂μ
        = ((∫ x, mtranslate x₀ h₀ x ∂μ : ℝ) : ℂ) from integral_ofReal, hψint,
      Complex.ofReal_one]
  refine ⟨fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ), hψcc, hψcs, ?_⟩
  -- the difference of transforms is `∫ ψ·u`
  have hdiff : fourierTransform μ (fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ)) χ
      - fourierTransform μ (fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ)) χ'
      = ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x ∂μ := by
    rw [fourierTransform_apply, fourierTransform_apply,
      ← integral_sub (hψci.mul_conj_char μ χ) (hψci.mul_conj_char μ χ')]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [hu]
    ring
  -- `∫ ψ·u` stays close to `u x₀`
  have hubdd : ∀ x, ‖u x‖ ≤ 2 := fun x => by
    rw [hu]
    calc ‖conj (χ x : ℂ) - conj ((χ' x : Circle) : ℂ)‖
        ≤ ‖conj (χ x : ℂ)‖ + ‖conj ((χ' x : Circle) : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
          rw [RCLike.norm_conj, RCLike.norm_conj, Circle.norm_coe, Circle.norm_coe]
          norm_num
  have hψui : Integrable (fun x => ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x) μ :=
    hψci.mul_bdd hucont.aestronglyMeasurable (Eventually.of_forall hubdd)
  have hconst : ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x₀ ∂μ = u x₀ := by
    rw [integral_mul_const, hψcint, one_mul]
  have hsub : (∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x ∂μ) - u x₀
      = ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x
          - ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x₀ ∂μ := by
    rw [integral_sub hψui (hψci.mul_const (u x₀)), hconst]
  have hclose : ‖(∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x ∂μ) - u x₀‖ ≤ ‖u x₀‖ / 2 := by
    rw [hsub]
    have hpt : ∀ x, ‖((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x
        - ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x₀‖ ≤ mtranslate x₀ h₀ x * (‖u x₀‖ / 2) := by
      intro x
      rw [← mul_sub, norm_mul]
      have hn : ‖((mtranslate x₀ h₀ x : ℝ) : ℂ)‖ = mtranslate x₀ h₀ x := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ0 x)]
      rw [hn]
      by_cases hx : x ∈ tsupport (mtranslate x₀ h₀)
      · exact mul_le_mul_of_nonneg_left (hψsupp hx).le (hψ0 x)
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp
    refine (norm_integral_le_of_norm_le
      ((hψc.integrable_of_hasCompactSupport hψs).mul_const _)
      (Eventually.of_forall hpt)).trans ?_
    rw [integral_mul_const, hψint, one_mul]
  -- conclude
  intro heq
  have hzero : ∫ x, ((mtranslate x₀ h₀ x : ℝ) : ℂ) * u x ∂μ = 0 := by
    rw [← hdiff, heq, sub_self]
  rw [hzero, zero_sub, norm_neg] at hclose
  linarith

/-- **Non-vanishing**: at every character `χ` there is a `C_c` function whose Fourier
transform equals `1` at `χ` (a normalized bump times the character). -/
theorem _root_.PontryaginDual.exists_fourierTransform_eq_one (χ : PontryaginDual G) :
    ∃ f : G → ℂ, Continuous f ∧ HasCompactSupport f ∧ fourierTransform μ f χ = 1 := by
  obtain ⟨h₀, hc, hs, h0, -, hint⟩ := exists_normalized_bump μ Set.univ Filter.univ_mem
  refine ⟨fun x => ((h₀ x : ℝ) : ℂ) * (χ x : ℂ),
    (Complex.continuous_ofReal.comp hc).mul
      (continuous_induced_dom.comp (map_continuous χ)),
    (hs.comp_left Complex.ofReal_zero).mul_right, ?_⟩
  rw [fourierTransform_apply]
  calc ∫ x, ((h₀ x : ℝ) : ℂ) * (χ x : ℂ) * conj (χ x : ℂ) ∂μ
      = ∫ x, ((h₀ x : ℝ) : ℂ) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show ((h₀ x : ℝ) : ℂ) * (χ x : ℂ) * conj (χ x : ℂ) = ((h₀ x : ℝ) : ℂ)
        rw [mul_assoc, Complex.mul_conj, Circle.normSq_coe]
        simp
    _ = 1 := by
        rw [show ∫ x, ((h₀ x : ℝ) : ℂ) ∂μ = ((∫ x, h₀ x ∂μ : ℝ) : ℂ) from integral_ofReal,
          hint, Complex.ofReal_one]

end Separation

/-! ### The character space of `L¹(G)` -/

section CharacterSpace

namespace L1G

/-- **Classification of the characters of `L¹(G)`**: every character `φ` of the convolution
algebra is evaluation of the Fourier transform at a unique character `χ` of `G`,
`φ F = 𝓕F(χ)`.  The proof is the translation-ratio argument: `q a := φ(Lₐ G₀) / φ(G₀)` is a
bounded continuous multiplicative function of modulus one, hence the conjugate of a character
of `G`, and the Bochner-integral form of convolution identifies `φ` with integration against
`q` on `C_c`; density does the rest. -/
theorem characterSpace_exists_char (φ : characterSpace ℂ (L1G μ)) :
    ∃! χ : PontryaginDual G, ∀ F : L1G μ, φ F = fourier μ F χ := by
  have hφcont : Continuous (⇑φ : L1G μ → ℂ) := map_continuous φ
  -- Step 0: a C_c class on which φ does not vanish
  obtain ⟨g₀, hg₀c, hg₀s, hG₀⟩ :
      ∃ (g₀ : G → ℂ) (hc : Continuous g₀) (hs : HasCompactSupport g₀),
        φ (ofLp μ (toLpCc μ g₀ hc hs)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine φ.prop.1 (DFunLike.ext _ _ fun F => ?_)
    have h1 := funext_of_dense μ (fun Fp => φ (ofLp μ Fp)) (fun _ => 0)
      hφcont continuous_const (fun f hfc hfs => hcon f hfc hfs) (toLp μ F)
    exact h1
  set G₀ : L1G μ := ofLp μ (toLpCc μ g₀ hg₀c hg₀s) with hG₀def
  -- Step 1: the translation ratio and its multiplicativity
  set q : G → ℂ := fun a => φ (translate μ a G₀) / φ G₀ with hq
  have hkey : ∀ (a : G) (F : L1G μ), φ (translate μ a F) = q a * φ F := by
    intro a F
    have h1 : φ (translate μ a (F * G₀)) = φ (translate μ a F) * φ G₀ := by
      rw [translate_mul μ a F G₀, _root_.map_mul φ]
    have h2 : φ (translate μ a (F * G₀)) = φ (translate μ a G₀) * φ F := by
      rw [mul_comm F G₀, translate_mul μ a G₀ F, _root_.map_mul φ]
    have h3 : φ (translate μ a F) * φ G₀ = φ (translate μ a G₀) * φ F := h1.symm.trans h2
    simp only [hq]
    field_simp
    linear_combination h3
  have hq1 : q 1 = 1 := by
    simp only [hq]
    rw [translate_one μ G₀, div_self hG₀]
  have hqmul : ∀ a b : G, q (a * b) = q a * q b := by
    intro a b
    have h2 : φ (translate μ (a * b) G₀) = q a * q b * φ G₀ := by
      rw [← translate_translate μ a b G₀, hkey a (translate μ b G₀), hkey b G₀]
      ring
    have h3 : q (a * b) * φ G₀ = q a * q b * φ G₀ := by
      rw [← hkey (a * b) G₀, h2]
    exact mul_right_cancel₀ hG₀ h3
  have hqcont : Continuous q := by
    simp only [hq]
    exact (hφcont.comp (continuous_translate μ G₀)).div_const _
  -- Step 2: boundedness forces modulus one
  have hqbdd : ∀ a : G, ‖q a‖ ≤ ‖toCLM φ‖ * ‖G₀‖ / ‖φ G₀‖ := by
    intro a
    have h1 : ‖φ (translate μ a G₀)‖ ≤ ‖toCLM φ‖ * ‖G₀‖ := by
      have h2 := (toCLM φ).le_opNorm (translate μ a G₀)
      rwa [coe_toCLM, norm_translate] at h2
    simp only [hq]
    rw [norm_div]
    gcongr
  have hqpow : ∀ (a : G) (n : ℕ), q (a ^ n) = q a ^ n := by
    intro a n
    induction n with
    | zero => simpa using hq1
    | succ n ih => rw [pow_succ, pow_succ, ← ih, ← hqmul]
  have hqle : ∀ a : G, ‖q a‖ ≤ 1 := by
    intro a
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖toCLM φ‖ * ‖G₀‖ / ‖φ G₀‖) hlt
    have h1 : ‖q (a ^ n)‖ ≤ ‖toCLM φ‖ * ‖G₀‖ / ‖φ G₀‖ := hqbdd (a ^ n)
    rw [hqpow a n, norm_pow] at h1
    exact absurd h1 (not_le.mpr hn)
  have hqinv : ∀ a : G, q a * q a⁻¹ = 1 := by
    intro a
    rw [← hqmul, mul_inv_cancel]
    exact hq1
  have hqnorm : ∀ a : G, ‖q a‖ = 1 := by
    intro a
    refine le_antisymm (hqle a) ?_
    have h1 : ‖q a‖ * ‖q a⁻¹‖ = 1 := by rw [← norm_mul, hqinv a, norm_one]
    nlinarith [hqle a⁻¹, norm_nonneg (q a), norm_nonneg (q a⁻¹)]
  -- Step 3: the character of `G` given by `conj ∘ q`
  set χ : PontryaginDual G :=
    { toFun := fun x => ⟨conj (q x), mem_sphere_zero_iff_norm.mpr
        (by rw [RCLike.norm_conj]; exact hqnorm x)⟩
      map_one' := Circle.ext (show conj (q 1) = 1 by rw [hq1, _root_.map_one])
      map_mul' := fun x y => Circle.ext
        (show conj (q (x * y)) = conj (q x) * conj (q y) by rw [hqmul, _root_.map_mul])
      continuous_toFun := Continuous.subtype_mk
        (Complex.continuous_conj.comp hqcont) _ } with hχ
  have hχconj : ∀ x : G, conj ((χ x : Circle) : ℂ) = q x := fun x => by
    simp only [hχ]
    exact Complex.conj_conj (q x)
  -- Step 4: `φ` is integration against `q` on `C_c`
  have hrep : ∀ (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f),
      φ (ofLp μ (toLpCc μ f hfc hfs)) = fourierTransform μ f χ := by
    intro f hfc hfs
    have hΦi : Integrable (fun a => f a • translateLp μ 1 a (toLpCc μ g₀ hg₀c hg₀s)) μ :=
      integrable_smul_translateLp μ f hfc hfs _
    have hkey2 := congrArg (⇑(toCLM φ))
      (toLpCc_mconv_eq_integral μ f g₀ hfc hfs hg₀c hg₀s)
    -- the left side is `φ(F_f) · φ(G₀)`
    have h1 : ofLp μ (toLpCc μ (mconv μ f g₀) (hfc.mconv μ hfs hg₀c hg₀s)
        (hfs.mconv μ hg₀s)) = ofLp μ (toLpCc μ f hfc hfs) * G₀ :=
      (congrArg (ofLp μ) (mulCLM_toLpCc μ f g₀ hfc hfs hg₀c hg₀s)).symm
    have hL : toCLM φ (toLpCc μ (mconv μ f g₀) (hfc.mconv μ hfs hg₀c hg₀s)
        (hfs.mconv μ hg₀s)) = φ (ofLp μ (toLpCc μ f hfc hfs)) * φ G₀ := by
      show φ (ofLp μ (toLpCc μ (mconv μ f g₀) _ _)) = _
      rw [h1, _root_.map_mul φ]
    -- the right side is `(∫ f·q) · φ(G₀)`
    have hpt : ∀ a : G, toCLM φ (f a • translateLp μ 1 a (toLpCc μ g₀ hg₀c hg₀s))
        = f a * q a * φ G₀ := by
      intro a
      have h4 : toCLM φ (f a • translateLp μ 1 a (toLpCc μ g₀ hg₀c hg₀s))
          = φ (f a • translate μ a G₀) := rfl
      rw [h4, map_smul φ, hkey a G₀, smul_eq_mul]
      ring
    have hR : toCLM φ (∫ a, f a • translateLp μ 1 a (toLpCc μ g₀ hg₀c hg₀s) ∂μ)
        = (∫ a, f a * q a ∂μ) * φ G₀ := by
      rw [← ContinuousLinearMap.integral_comp_comm (toCLM φ) hΦi,
        integral_congr_ae (Eventually.of_forall hpt), integral_mul_const]
    have hEq : φ (ofLp μ (toLpCc μ f hfc hfs)) * φ G₀ = (∫ a, f a * q a ∂μ) * φ G₀ := by
      rw [← hL, ← hR]
      exact hkey2
    have hφf : φ (ofLp μ (toLpCc μ f hfc hfs)) = ∫ a, f a * q a ∂μ :=
      mul_right_cancel₀ hG₀ hEq
    rw [hφf, fourierTransform_apply]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show f a * q a = f a * conj ((χ a : Circle) : ℂ)
    rw [hχconj a]
  -- Step 5: density extends the representation to all of L¹
  have hall : ∀ F : L1G μ, φ F = fourier μ F χ := fun F =>
    funext_of_dense μ (fun Fp => φ (ofLp μ Fp)) (fun Fp => fourierTransform μ ⇑Fp χ)
      hφcont (continuous_fourierTransform_coeFn μ χ)
      (fun f hfc hfs => by
        rw [fourierTransform_coeFn_toLpCc μ f hfc hfs]
        exact hrep f hfc hfs) (toLp μ F)
  -- uniqueness, by separation
  refine ⟨χ, hall, ?_⟩
  intro χ' hχ'
  by_contra hne
  obtain ⟨f, hfc, hfs, hsep⟩ := fourierTransform_separates μ hne
  have h1 : fourierTransform μ f χ' = fourierTransform μ f χ := by
    have e1 := (hχ' (ofLp μ (toLpCc μ f hfc hfs))).symm.trans
      (hall (ofLp μ (toLpCc μ f hfc hfs)))
    rwa [fourier_ofLp_toLpCc μ f hfc hfs] at e1
  exact hsep h1

end L1G

end CharacterSpace

end MeasureTheory

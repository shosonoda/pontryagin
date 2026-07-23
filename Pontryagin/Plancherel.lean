/-
Copyright (c) 2026 The pontryagin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The pontryagin contributors
-/
import Pontryagin.Inversion
import Pontryagin.DensityLp
import Pontryagin.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Plancherel theory and localized Fourier transforms

For a locally compact Hausdorff abelian group `G` with regular Haar measure `μ` and dual Haar
measure `dualHaar μ` on the Pontryagin dual `Ĝ = PontryaginDual G` (`Pontryagin.Inversion`),
this file develops the `L²` theory of the Fourier transform.

## Main results

* `exists_cc_close_L1_L2`: a function in `L¹ ∩ L²` can be approximated by a single continuous
  compactly supported function simultaneously in the `L¹` and `L²` norms (truncation in range,
  `C_c`-approximation in `L¹`, and clamping back into the ball of bounded functions).
* `mconv_ae_eq_mulCLM`: for `f, g ∈ L¹ ∩ L²`, the pointwise convolution `mconv μ f g` is an
  almost-everywhere representative of the abstract `L¹`-algebra product `mulCLM`.
* `integral_norm_sq_fourierTransform` (**Parseval/Plancherel identity**): for `f ∈ L¹ ∩ L²`,
  `∫ ‖𝓕f‖² ∂(dualHaar μ) = ∫ ‖f‖² ∂μ`, together with `memLp_two_fourierTransform`.
* `plancherelLI : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 (dualHaar μ)` (**the Plancherel isometry**): the
  extension of `F ↦ class of 𝓕(representative)` from the dense subspace of `C_c` classes,
  with agreement lemmas `plancherelLI_toLp2Cc` and `plancherelLI_memLp_toLp`.
* `surjective_plancherelLI`: the Plancherel isometry is **surjective**.  The range is closed
  (isometric image of a complete space); its orthogonal complement vanishes by the dual
  uniqueness theorem `ae_eq_zero_of_forall_integral_char_mul_eq_zero` (an integrable density
  on `Ĝ` all whose "inverse Fourier coefficients" vanish is a.e. zero) together with the
  admissible squares of `Pontryagin.Inversion`.
* `exists_integrable_fourierTransform_eq_zero_compl` (**localized transforms**): for every
  nonempty open `Ω ⊆ Ĝ` there is an integrable `Φ : G → ℂ` whose Fourier transform is not
  identically zero but vanishes outside `Ω`.  `Φ` is the pointwise product of the Plancherel
  preimages of two indicator functions, and `𝓕Φ` is computed *exactly* as the convolution of
  the two indicators on the dual, by polarization of the Plancherel identity.
-/

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ComplexConjugate ComplexOrder ENNReal NNReal Pointwise ZeroAtInfty

-- The sections below deliberately use one coarse hypothesis block (locally compact Hausdorff
-- abelian group with regular Haar measure) rather than minimal per-lemma assumptions.
set_option linter.unusedSectionVars false

-- `show` is used pervasively to beta-reduce integrands.
set_option linter.style.show false

/-! ### The clamp inequality on `ℂ`

Radial truncation at level `M` (implemented as multiplication by `M / max ‖z‖ M`) moves a
point closer to every point of the closed ball of radius `M`. -/

section Clamp

/-- Radial clamping to the ball of radius `M` is a contraction towards points of the ball:
if `‖w‖ ≤ M` then `‖w - (M / max ‖z‖ M) • z‖ ≤ ‖w - z‖`. -/
theorem norm_sub_smul_div_max_le {M : ℝ} (hM : 0 < M) (w z : ℂ) (hw : ‖w‖ ≤ M) :
    ‖w - (M / max ‖z‖ M) • z‖ ≤ ‖w - z‖ := by
  rcases le_or_gt ‖z‖ M with hzM | hzM
  · rw [max_eq_right hzM, div_self hM.ne', one_smul]
  · set c : ℝ := M / max ‖z‖ M with hcdef
    have hmax : max ‖z‖ M = ‖z‖ := max_eq_left hzM.le
    have hz0 : (0 : ℝ) < ‖z‖ := hM.trans hzM
    have hc0 : 0 ≤ c := by
      rw [hcdef]
      positivity
    have hc1 : c ≤ 1 := by
      rw [hcdef, hmax, div_le_one hz0]
      exact hzM.le
    have hcz : c * ‖z‖ = M := by
      rw [hcdef, hmax, div_mul_cancel₀ _ hz0.ne']
    -- the real part of `w * conj z` is at most `M * ‖z‖`
    have ht : (w * conj z).re ≤ M * ‖z‖ := by
      calc (w * conj z).re ≤ ‖w * conj z‖ :=
            (le_abs_self _).trans (Complex.abs_re_le_norm _)
        _ = ‖w‖ * ‖z‖ := by rw [norm_mul, RCLike.norm_conj]
        _ ≤ M * ‖z‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg z)
    -- expansion of the two squared norms
    have hexp : ∀ t : ℝ, ‖w - t • z‖ ^ 2
        = ‖w‖ ^ 2 + t ^ 2 * ‖z‖ ^ 2 - 2 * (t * (w * conj z).re) := by
      intro t
      have h1 : conj ((t : ℂ) * z) = (t : ℂ) * conj z := by
        rw [map_mul, Complex.conj_ofReal]
      have h2 : (w * ((t : ℂ) * conj z)).re = t * (w * conj z).re := by
        rw [mul_left_comm, Complex.re_ofReal_mul]
      calc ‖w - t • z‖ ^ 2
          = Complex.normSq (w - (t : ℂ) * z) := by
            rw [← Complex.normSq_eq_norm_sq, Complex.real_smul]
        _ = Complex.normSq w + Complex.normSq ((t : ℂ) * z)
              - 2 * (w * conj ((t : ℂ) * z)).re := Complex.normSq_sub w _
        _ = ‖w‖ ^ 2 + t ^ 2 * ‖z‖ ^ 2 - 2 * (t * (w * conj z).re) := by
            rw [h1, h2, Complex.normSq_mul, Complex.normSq_ofReal,
              Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
            ring
    have hsq : ‖w - c • z‖ ^ 2 ≤ ‖w - z‖ ^ 2 := by
      have h1 := hexp c
      have h2 : ‖w - z‖ ^ 2 = ‖w‖ ^ 2 + ‖z‖ ^ 2 - 2 * (w * conj z).re := by
        have := hexp 1
        simpa using this
      rw [h1, h2]
      nlinarith [sq_nonneg (‖z‖ - M), mul_nonneg (sub_nonneg.mpr hc1)
        (sub_nonneg.mpr ht), norm_nonneg z]
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq

end Clamp

/-! ### Bridges between `eLpNorm _ 2` and integrals of squared norms -/

section L2Bridges

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- If the integral of the squared norm is at most `ε ^ 2`, the `L²` seminorm is at most
`ENNReal.ofReal ε`. -/
theorem eLpNorm_two_le_ofReal {h : X → ℂ} (hh : MemLp h 2 ν) {ε : ℝ} (hε : 0 ≤ ε)
    (hle : ∫ x, ‖h x‖ ^ 2 ∂ν ≤ ε ^ 2) : eLpNorm h 2 ν ≤ ENNReal.ofReal ε := by
  have hI0 : 0 ≤ ∫ x, ‖h x‖ ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  have hint : ∫ x, ‖h x‖ ^ (2 : ℝ≥0∞).toReal ∂ν = ∫ x, ‖h x‖ ^ 2 ∂ν := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ‖h x‖ ^ (2 : ℝ≥0∞).toReal = ‖h x‖ ^ 2
    rw [ENNReal.toReal_ofNat, ← Real.rpow_natCast ‖h x‖ 2]
    norm_num
  rw [hh.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, hint]
  refine ENNReal.ofReal_le_ofReal ?_
  have hexp : ((2 : ℝ≥0∞).toReal)⁻¹ = (2 : ℝ)⁻¹ := by rw [ENNReal.toReal_ofNat]
  rw [hexp]
  calc (∫ x, ‖h x‖ ^ 2 ∂ν) ^ ((2 : ℝ)⁻¹)
      ≤ (ε ^ 2) ^ ((2 : ℝ)⁻¹) := Real.rpow_le_rpow hI0 hle (by norm_num)
    _ = ε := by
        rw [show ε ^ 2 = ε ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast],
          ← Real.rpow_mul hε]
        norm_num

/-- The squared norm of an `L²` class is the integral of the squared norm of a
representative. -/
theorem norm_toLp_two_sq {h : X → ℂ} (hh : MemLp h 2 ν) :
    ‖hh.toLp h‖ ^ 2 = ∫ x, ‖h x‖ ^ 2 ∂ν := by
  have hI0 : 0 ≤ ∫ x, ‖h x‖ ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  have hint : ∫ x, ‖h x‖ ^ (2 : ℝ≥0∞).toReal ∂ν = ∫ x, ‖h x‖ ^ 2 ∂ν := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ‖h x‖ ^ (2 : ℝ≥0∞).toReal = ‖h x‖ ^ 2
    rw [ENNReal.toReal_ofNat, ← Real.rpow_natCast ‖h x‖ 2]
    norm_num
  have hexp : ((2 : ℝ≥0∞).toReal)⁻¹ = (2 : ℝ)⁻¹ := by rw [ENNReal.toReal_ofNat]
  rw [Lp.norm_toLp, hh.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    hint, hexp, ENNReal.toReal_ofReal (Real.rpow_nonneg hI0 _)]
  rw [show ((∫ x, ‖h x‖ ^ 2 ∂ν) ^ ((2 : ℝ)⁻¹)) ^ 2
      = ((∫ x, ‖h x‖ ^ 2 ∂ν) ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast],
    ← Real.rpow_mul hI0]
  norm_num

/-- Two `L²` classes whose representatives have the same integral of the squared norm have
the same norm. -/
theorem norm_toLp_two_eq_of_integral_sq_eq {h : X → ℂ} {Y : Type*} [MeasurableSpace Y]
    {σ : Measure Y} {k : Y → ℂ} (hh : MemLp h 2 ν) (hk : MemLp k 2 σ)
    (heq : ∫ x, ‖h x‖ ^ 2 ∂ν = ∫ y, ‖k y‖ ^ 2 ∂σ) :
    ‖hh.toLp h‖ = ‖hk.toLp k‖ := by
  have h1 : ‖hh.toLp h‖ ^ 2 = ‖hk.toLp k‖ ^ 2 := by
    rw [norm_toLp_two_sq hh, norm_toLp_two_sq hk, heq]
  calc ‖hh.toLp h‖ = Real.sqrt (‖hh.toLp h‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖hk.toLp k‖ ^ 2) := by rw [h1]
    _ = ‖hk.toLp k‖ := Real.sqrt_sq (norm_nonneg _)

end L2Bridges

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-! ### Simultaneous `L¹`/`L²` approximation by truncation and clamping -/

section SimultaneousApproximation

/-- **Truncation step**: a function in `L¹ ∩ L²` can be approximated simultaneously in `L¹`
and (squared) `L²` by a bounded function (its truncation to a sublevel set of the norm). -/
private theorem exists_bounded_close_L1_L2 {f : G → ℂ} (hf1 : Integrable f μ)
    (hf2 : MemLp f 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : G → ℂ, Integrable g μ ∧ MemLp g 2 μ ∧
      (∃ M : ℝ, 0 < M ∧ ∀ x, ‖g x‖ ≤ M) ∧
      (∫ x, ‖f x - g x‖ ∂μ) ≤ ε ∧ ∫ x, ‖f x - g x‖ ^ 2 ∂μ ≤ ε ^ 2 := by
  -- pass to a strongly measurable representative
  set f' : G → ℂ := hf2.1.mk f with hf'def
  have hf'sm : StronglyMeasurable f' := hf2.1.stronglyMeasurable_mk
  have hff' : f =ᵐ[μ] f' := hf2.1.ae_eq_mk
  have hf'1 : Integrable f' μ := hf1.congr hff'
  have hf'2 : MemLp f' 2 μ := hf2.ae_eq hff'
  have hf'sq : Integrable (fun x => ‖f' x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf'2.1).mp hf'2
  -- the truncations
  set A : ℕ → Set G := fun n => {x | ‖f' x‖ ≤ (n : ℝ)} with hAdef
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_le hf'sm.measurable.norm measurable_const
  set g : ℕ → G → ℂ := fun n => (A n).indicator f' with hgdef
  have hgsm : ∀ n, StronglyMeasurable (g n) := fun n => hf'sm.indicator (hAmeas n)
  have hgb : ∀ n x, ‖g n x‖ ≤ (n : ℝ) := by
    intro n x
    by_cases hx : x ∈ A n
    · rw [hgdef]
      simp only [Set.indicator_of_mem hx]
      exact hx
    · rw [hgdef]
      simp only [Set.indicator_of_notMem hx, norm_zero]
      exact Nat.cast_nonneg n
  have hgle : ∀ n x, ‖g n x‖ ≤ ‖f' x‖ := by
    intro n x
    by_cases hx : x ∈ A n
    · rw [hgdef]
      simp [Set.indicator_of_mem hx]
    · rw [hgdef]
      simp [Set.indicator_of_notMem hx]
  have hg1 : ∀ n, Integrable (g n) μ := fun n => hf'1.indicator (hAmeas n)
  have hg2 : ∀ n, MemLp (g n) 2 μ := fun n =>
    hf'2.of_le (hgsm n).aestronglyMeasurable (Eventually.of_forall (hgle n))
  -- pointwise convergence of the truncation errors
  have hlim : ∀ x : G, Tendsto (fun n : ℕ => f' x - g n x) atTop (𝓝 0) := by
    intro x
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop ⌈‖f' x‖⌉₊] with n hn
    have hx : x ∈ A n := by
      show ‖f' x‖ ≤ (n : ℝ)
      exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [hgdef]
    simp [Set.indicator_of_mem hx]
  -- `L¹` convergence
  have hT1 : Tendsto (fun n => ∫ x, ‖f' x - g n x‖ ∂μ) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _x, (0 : ℝ) ∂μ := by rw [integral_zero]
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f' x‖)
      (fun n => (hf'sm.sub (hgsm n)).norm.aestronglyMeasurable) hf'1.norm
      (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      by_cases hx : x ∈ A n
      · rw [hgdef]
        simp [Set.indicator_of_mem hx]
      · rw [hgdef]
        simp [Set.indicator_of_notMem hx]
    · have h2 : Tendsto (fun n : ℕ => ‖f' x - g n x‖) atTop (𝓝 ‖(0 : ℂ)‖) :=
        (continuous_norm.tendsto (0 : ℂ)).comp (hlim x)
      simpa [Function.comp_def] using h2
  -- squared `L²` convergence
  have hT2 : Tendsto (fun n => ∫ x, ‖f' x - g n x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _x, (0 : ℝ) ∂μ := by rw [integral_zero]
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f' x‖ ^ 2)
      (fun n => ((hf'sm.sub (hgsm n)).norm.aestronglyMeasurable.aemeasurable.pow_const
        2).aestronglyMeasurable) hf'sq
      (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hx : x ∈ A n
      · rw [hgdef]
        simp [Set.indicator_of_mem hx]
      · rw [hgdef]
        simp only [Set.indicator_of_notMem hx, sub_zero, le_refl]
    · have h1 : Tendsto (fun n : ℕ => ‖f' x - g n x‖) atTop (𝓝 0) := by
        have := (continuous_norm.tendsto (0 : ℂ)).comp (hlim x)
        simpa [Function.comp_def] using this
      have h2 : Tendsto (fun n : ℕ => ‖f' x - g n x‖ ^ 2) atTop (𝓝 (0 ^ 2)) := h1.pow 2
      simpa using h2
  -- pick a single index good for both
  have hev : ∀ᶠ n in atTop, (∫ x, ‖f' x - g n x‖ ∂μ) < ε ∧
      (∫ x, ‖f' x - g n x‖ ^ 2 ∂μ) < ε ^ 2 :=
    (hT1.eventually_lt_const hε).and (hT2.eventually_lt_const (by positivity))
  obtain ⟨n, hn1, hn2⟩ := hev.exists
  refine ⟨g n, hg1 n, hg2 n, ⟨(n : ℝ) + 1, by positivity,
    fun x => (hgb n x).trans (by linarith)⟩, ?_, ?_⟩
  · calc ∫ x, ‖f x - g n x‖ ∂μ
        = ∫ x, ‖f' x - g n x‖ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hff'] with x hx
          rw [hx]
      _ ≤ ε := hn1.le
  · calc ∫ x, ‖f x - g n x‖ ^ 2 ∂μ
        = ∫ x, ‖f' x - g n x‖ ^ 2 ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hff'] with x hx
          rw [hx]
      _ ≤ ε ^ 2 := hn2.le

/-- **Simultaneous `L¹` and `L²` approximation by `C_c` functions.**  A function in
`L¹ ∩ L²` is within `ε` of a continuous compactly supported function in both norms at once:
truncate the range, approximate in `L¹`, and clamp the approximant back into the ball. -/
theorem exists_cc_close_L1_L2 {f : G → ℂ} (hf1 : Integrable f μ) (hf2 : MemLp f 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : G → ℂ, Continuous v ∧ HasCompactSupport v ∧
      (∫ x, ‖f x - v x‖ ∂μ) ≤ ε ∧ eLpNorm (fun x => f x - v x) 2 μ ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hg1, hg2, ⟨M, hM, hgb⟩, hgL1, hgL2⟩ :=
    exists_bounded_close_L1_L2 μ hf1 hf2 (show (0 : ℝ) < ε / 2 by linarith)
  -- the `L¹` approximation of the bounded truncation
  set δ : ℝ := min (ε / 2) ((ε / 2) ^ 2 / (2 * M)) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by positivity)
  obtain ⟨v₀, hv₀c, hv₀s, hv₀i, hv₀close⟩ :=
    exists_hasCompactSupport_integral_norm_sub_le hg1 hδ0
  -- the clamp
  set v : G → ℂ := fun x => (M / max ‖v₀ x‖ M) • v₀ x with hvdef
  have hmaxpos : ∀ x, (0 : ℝ) < max ‖v₀ x‖ M := fun x =>
    lt_of_lt_of_le hM (le_max_right _ _)
  have hvc : Continuous v := by
    refine Continuous.smul (continuous_const.div ((hv₀c.norm).max continuous_const)
      fun x => (hmaxpos x).ne') hv₀c
  have hvs : HasCompactSupport v := by
    refine hv₀s.mono fun x hx => ?_
    simp only [mem_support] at hx ⊢
    intro h0
    exact hx (by rw [hvdef]; show (M / max ‖v₀ x‖ M) • v₀ x = 0; rw [h0, smul_zero])
  have hvb : ∀ x, ‖v x‖ ≤ M := by
    intro x
    rw [hvdef]
    show ‖(M / max ‖v₀ x‖ M) • v₀ x‖ ≤ M
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hM.le (hmaxpos x).le)]
    calc M / max ‖v₀ x‖ M * ‖v₀ x‖
        ≤ M / max ‖v₀ x‖ M * max ‖v₀ x‖ M :=
          mul_le_mul_of_nonneg_left (le_max_left _ _)
            (div_nonneg hM.le (hmaxpos x).le)
      _ = M := div_mul_cancel₀ M (hmaxpos x).ne'
  have hvint : Integrable v μ := hvc.integrable_of_hasCompactSupport hvs
  have hvL2 : MemLp v 2 μ := hvc.memLp_of_hasCompactSupport hvs
  -- pointwise contraction
  have hcontract : ∀ x, ‖g x - v x‖ ≤ ‖g x - v₀ x‖ := fun x =>
    norm_sub_smul_div_max_le hM (g x) (v₀ x) (hgb x)
  -- `L¹` estimate for `g - v`
  have hgvL1 : ∫ x, ‖g x - v x‖ ∂μ ≤ δ := by
    calc ∫ x, ‖g x - v x‖ ∂μ
        ≤ ∫ x, ‖g x - v₀ x‖ ∂μ :=
          integral_mono (hg1.sub hvint).norm (hg1.sub hv₀i).norm hcontract
      _ ≤ δ := hv₀close
  -- squared `L²` estimate for `g - v`
  have hgvsq : ∫ x, ‖g x - v x‖ ^ 2 ∂μ ≤ (ε / 2) ^ 2 := by
    have hpt : ∀ x, ‖g x - v x‖ ^ 2 ≤ 2 * M * ‖g x - v₀ x‖ := by
      intro x
      have h1 : ‖g x - v x‖ ≤ 2 * M := by
        calc ‖g x - v x‖ ≤ ‖g x‖ + ‖v x‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hgb x) (hvb x)
          _ = 2 * M := by ring
      calc ‖g x - v x‖ ^ 2 = ‖g x - v x‖ * ‖g x - v x‖ := by ring
        _ ≤ (2 * M) * ‖g x - v₀ x‖ :=
            mul_le_mul h1 (hcontract x) (norm_nonneg _) (by positivity)
    have hsqint : Integrable (fun x => ‖g x - v x‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm (hg2.sub hvL2).1).mp (hg2.sub hvL2)
    calc ∫ x, ‖g x - v x‖ ^ 2 ∂μ
        ≤ ∫ x, 2 * M * ‖g x - v₀ x‖ ∂μ :=
          integral_mono hsqint ((hg1.sub hv₀i).norm.const_mul _) hpt
      _ = 2 * M * ∫ x, ‖g x - v₀ x‖ ∂μ := integral_const_mul _ _
      _ ≤ 2 * M * ((ε / 2) ^ 2 / (2 * M)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hv₀close.trans (min_le_right _ _)
      _ = (ε / 2) ^ 2 := by field_simp
  refine ⟨v, hvc, hvs, ?_, ?_⟩
  · -- combined `L¹` estimate
    calc ∫ x, ‖f x - v x‖ ∂μ
        ≤ ∫ x, (‖f x - g x‖ + ‖g x - v x‖) ∂μ := by
          refine integral_mono (hf1.sub hvint).norm
            ((hf1.sub hg1).norm.add (hg1.sub hvint).norm) fun x => ?_
          calc ‖f x - v x‖ = ‖(f x - g x) + (g x - v x)‖ := by ring_nf
            _ ≤ ‖f x - g x‖ + ‖g x - v x‖ := norm_add_le _ _
      _ = (∫ x, ‖f x - g x‖ ∂μ) + ∫ x, ‖g x - v x‖ ∂μ :=
          integral_add (hf1.sub hg1).norm (hg1.sub hvint).norm
      _ ≤ ε / 2 + δ := add_le_add hgL1 hgvL1
      _ ≤ ε / 2 + ε / 2 := by
          have := min_le_left (ε / 2) ((ε / 2) ^ 2 / (2 * M))
          linarith
      _ = ε := by ring
  · -- combined `L²` estimate
    have h1 : eLpNorm (fun x => f x - g x) 2 μ ≤ ENNReal.ofReal (ε / 2) :=
      eLpNorm_two_le_ofReal (hf2.sub hg2) (by linarith) hgL2
    have h2 : eLpNorm (fun x => g x - v x) 2 μ ≤ ENNReal.ofReal (ε / 2) :=
      eLpNorm_two_le_ofReal (hg2.sub hvL2) (by linarith) hgvsq
    have hsplit : (fun x => f x - v x)
        = (fun x => f x - g x) + fun x => g x - v x := by
      funext x
      show f x - v x = (f x - g x) + (g x - v x)
      ring
    calc eLpNorm (fun x => f x - v x) 2 μ
        = eLpNorm ((fun x => f x - g x) + fun x => g x - v x) 2 μ := by rw [hsplit]
      _ ≤ eLpNorm (fun x => f x - g x) 2 μ + eLpNorm (fun x => g x - v x) 2 μ :=
          eLpNorm_add_le (hf2.sub hg2).1 (hg2.sub hvL2).1 one_le_two
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add h1 h2
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          norm_num

end SimultaneousApproximation

/-! ### Consistency of the pointwise `L²` convolution with the `L¹`-algebra product -/

section ConvolutionConsistency

/-- The convolution integrand of two `L²` functions is integrable (Cauchy–Schwarz). -/
theorem integrable_mconv_integrand_L2 {p q : G → ℂ} (hp : MemLp p 2 μ)
    (hq : MemLp q 2 μ) (x : G) : Integrable (fun y => p y * q (y⁻¹ * x)) μ :=
  hp.integrable_mul (memLp_two_shift μ hq x)

set_option maxHeartbeats 1000000 in
-- Unifying the Hölder-triple integrability of the convolution integrands with the
-- beta-reduced integrands is expensive.
/-- Bilinear splitting of a difference of convolutions of `L²` functions. -/
private theorem mconv_sub_split {f g v w : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) (x : G) :
    mconv μ v w x - mconv μ f g x
      = mconv μ (fun y => v y - f y) w x + mconv μ f (fun y => w y - g y) x := by
  have h1 : mconv μ (fun y => v y - f y) w x = mconv μ v w x - mconv μ f w x := by
    show ∫ y, (v y - f y) * w (y⁻¹ * x) ∂μ = _
    rw [show ∫ y, (v y - f y) * w (y⁻¹ * x) ∂μ
        = ∫ y, (v y * w (y⁻¹ * x) - f y * w (y⁻¹ * x)) ∂μ from
      integral_congr_ae (Eventually.of_forall fun y => by ring)]
    exact integral_sub (integrable_mconv_integrand_L2 μ hv hw x)
      (integrable_mconv_integrand_L2 μ hf hw x)
  have h2 : mconv μ f (fun y => w y - g y) x = mconv μ f w x - mconv μ f g x := by
    show ∫ y, f y * (w (y⁻¹ * x) - g (y⁻¹ * x)) ∂μ = _
    rw [show ∫ y, f y * (w (y⁻¹ * x) - g (y⁻¹ * x)) ∂μ
        = ∫ y, (f y * w (y⁻¹ * x) - f y * g (y⁻¹ * x)) ∂μ from
      integral_congr_ae (Eventually.of_forall fun y => by ring)]
    exact integral_sub (integrable_mconv_integrand_L2 μ hf hw x)
      (integrable_mconv_integrand_L2 μ hf hg x)
  rw [h1, h2]
  ring

set_option maxHeartbeats 1600000 in
-- A long approximation argument: simultaneous `L¹`/`L²` limits, an a.e. convergent
-- subsequence, and pointwise limits of convolutions are combined in a single proof.
/-- **Consistency of `mconv` with the `L¹`-algebra multiplication**: for `f, g ∈ L¹ ∩ L²`,
the (everywhere-defined, continuous) pointwise convolution `mconv μ f g` is an a.e.
representative of the abstract product `mulCLM μ` of the `L¹` classes. -/
theorem mconv_ae_eq_mulCLM {f g : G → ℂ} (hf1 : Integrable f μ) (hf2 : MemLp f 2 μ)
    (hg1 : Integrable g μ) (hg2 : MemLp g 2 μ) :
    mconv μ f g =ᵐ[μ] ⇑(mulCLM μ (hf1.toL1 f) (hg1.toL1 g)) := by
  -- simultaneous `C_c` approximations of `f` and `g`
  have hv' : ∀ n : ℕ, ∃ v : G → ℂ, Continuous v ∧ HasCompactSupport v ∧
      (∫ x, ‖f x - v x‖ ∂μ) ≤ 1 / (n + 1) ∧
      eLpNorm (fun x => f x - v x) 2 μ ≤ ENNReal.ofReal (1 / (n + 1)) := fun n =>
    exists_cc_close_L1_L2 μ hf1 hf2 (by positivity)
  have hw' : ∀ n : ℕ, ∃ w : G → ℂ, Continuous w ∧ HasCompactSupport w ∧
      (∫ x, ‖g x - w x‖ ∂μ) ≤ 1 / (n + 1) ∧
      eLpNorm (fun x => g x - w x) 2 μ ≤ ENNReal.ofReal (1 / (n + 1)) := fun n =>
    exists_cc_close_L1_L2 μ hg1 hg2 (by positivity)
  choose v hvc hvs hv1 hv2 using hv'
  choose w hwc hws hw1 hw2 using hw'
  have hone : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have honele : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hVL2 : ∀ n, MemLp (v n) 2 μ := fun n =>
    (hvc n).memLp_of_hasCompactSupport (hvs n)
  have hWL2 : ∀ n, MemLp (w n) 2 μ := fun n =>
    (hwc n).memLp_of_hasCompactSupport (hws n)
  set Cf : ℝ := (eLpNorm f 2 μ).toReal with hCfdef
  set CK : ℝ := (eLpNorm g 2 μ).toReal with hCKdef
  -- `L²` error bounds, in real form
  have hvL2r : ∀ n, (eLpNorm (fun y => v n y - f y) 2 μ).toReal ≤ 1 / (n + 1) := by
    intro n
    have h1 : eLpNorm (fun y => v n y - f y) 2 μ = eLpNorm (fun y => f y - v n y) 2 μ :=
      eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_sub_rev _ _)
    rw [h1]
    calc (eLpNorm (fun y => f y - v n y) 2 μ).toReal
        ≤ (ENNReal.ofReal (1 / (n + 1))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hv2 n)
      _ = 1 / (n + 1) := ENNReal.toReal_ofReal (hone n).le
  have hwL2r : ∀ n, (eLpNorm (fun y => w n y - g y) 2 μ).toReal ≤ 1 / (n + 1) := by
    intro n
    have h1 : eLpNorm (fun y => w n y - g y) 2 μ = eLpNorm (fun y => g y - w n y) 2 μ :=
      eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_sub_rev _ _)
    rw [h1]
    calc (eLpNorm (fun y => g y - w n y) 2 μ).toReal
        ≤ (ENNReal.ofReal (1 / (n + 1))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hw2 n)
      _ = 1 / (n + 1) := ENNReal.toReal_ofReal (hone n).le
  -- the `L²` norms of the `w n` are uniformly bounded
  have hwn : ∀ n, (eLpNorm (w n) 2 μ).toReal ≤ CK + 1 := by
    intro n
    have hsplit : eLpNorm (w n) 2 μ
        ≤ eLpNorm g 2 μ + ENNReal.ofReal (1 / (n + 1)) := by
      have heq : w n = fun x => g x + (w n x - g x) := by
        funext x
        ring
      calc eLpNorm (w n) 2 μ
          = eLpNorm (fun x => g x + (w n x - g x)) 2 μ := by rw [← heq]
        _ ≤ eLpNorm g 2 μ + eLpNorm (fun x => w n x - g x) 2 μ :=
            eLpNorm_add_le hg2.1 ((hWL2 n).sub hg2).1 one_le_two
        _ ≤ eLpNorm g 2 μ + ENNReal.ofReal (1 / (n + 1)) := by
            refine add_le_add le_rfl ?_
            have h1 : eLpNorm (fun y => w n y - g y) 2 μ
                = eLpNorm (fun y => g y - w n y) 2 μ :=
              eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_sub_rev _ _)
            rw [h1]
            exact hw2 n
    have hne : eLpNorm g 2 μ + ENNReal.ofReal (1 / (n + 1)) ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨hg2.2.ne, ENNReal.ofReal_ne_top⟩
    calc (eLpNorm (w n) 2 μ).toReal
        ≤ (eLpNorm g 2 μ + ENNReal.ofReal (1 / (n + 1))).toReal :=
          ENNReal.toReal_mono hne hsplit
      _ = CK + (ENNReal.ofReal (1 / (n + 1))).toReal := by
          rw [ENNReal.toReal_add hg2.2.ne ENNReal.ofReal_ne_top]
      _ ≤ CK + 1 := by
          rw [ENNReal.toReal_ofReal (hone n).le]
          linarith [honele n]
  -- pointwise (in fact uniform) convergence of the convolutions
  have hBn : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * (CK + 1) + Cf * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 := (h.mul_const (CK + 1)).add (h.const_mul Cf)
    simpa only [zero_mul, mul_zero, add_zero] using h2
  have hunif : ∀ x, Tendsto (fun n => mconv μ (v n) (w n) x) atTop
      (𝓝 (mconv μ f g x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hBn
    have hsplit := mconv_sub_split μ hf2 hg2 (hVL2 n) (hWL2 n) x
    calc ‖mconv μ (v n) (w n) x - mconv μ f g x‖
        = ‖mconv μ (fun y => v n y - f y) (w n) x
            + mconv μ f (fun y => w n y - g y) x‖ := by rw [hsplit]
      _ ≤ ‖mconv μ (fun y => v n y - f y) (w n) x‖
            + ‖mconv μ f (fun y => w n y - g y) x‖ := norm_add_le _ _
      _ ≤ (eLpNorm (fun y => v n y - f y) 2 μ).toReal * (eLpNorm (w n) 2 μ).toReal
            + (eLpNorm f 2 μ).toReal
              * (eLpNorm (fun y => w n y - g y) 2 μ).toReal :=
          add_le_add (norm_mconv_le_of_memLp_two μ ((hVL2 n).sub hf2) (hWL2 n) x)
            (norm_mconv_le_of_memLp_two μ hf2 ((hWL2 n).sub hg2) x)
      _ ≤ 1 / ((n : ℝ) + 1) * (CK + 1) + Cf * (1 / ((n : ℝ) + 1)) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul (hvL2r n) (hwn n) ENNReal.toReal_nonneg (hone n).le
          · exact mul_le_mul_of_nonneg_left (hwL2r n) ENNReal.toReal_nonneg
  -- convergence of the classes in `L¹`
  set Fn : ℕ → Lp ℂ 1 μ := fun n => toLpCc μ (v n) (hvc n) (hvs n) with hFndef
  set Kn : ℕ → Lp ℂ 1 μ := fun n => toLpCc μ (w n) (hwc n) (hws n) with hKndef
  set F : Lp ℂ 1 μ := hf1.toL1 f with hFdef
  set K : Lp ℂ 1 μ := hg1.toL1 g with hKdef
  have hFn1 : ∀ n, ‖F - Fn n‖ ≤ 1 / (n + 1) := by
    intro n
    rw [norm_sub_eq_integral μ]
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (hv1 n)
    filter_upwards [hf1.coeFn_toL1, coeFn_toLpCc μ (v n) (hvc n) (hvs n)] with x hx1 hx2
    rw [hFdef, hFndef]
    show ‖(hf1.toL1 f) x - (toLpCc μ (v n) (hvc n) (hvs n)) x‖ = ‖f x - v n x‖
    rw [hx1, hx2]
  have hKn1 : ∀ n, ‖K - Kn n‖ ≤ 1 / (n + 1) := by
    intro n
    rw [norm_sub_eq_integral μ]
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (hw1 n)
    filter_upwards [hg1.coeFn_toL1, coeFn_toLpCc μ (w n) (hwc n) (hws n)] with x hx1 hx2
    rw [hKdef, hKndef]
    show ‖(hg1.toL1 g) x - (toLpCc μ (w n) (hwc n) (hws n)) x‖ = ‖g x - w n x‖
    rw [hx1, hx2]
  have hFtend : Tendsto Fn atTop (𝓝 F) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [norm_sub_rev]
    exact hFn1 n
  have hKtend : Tendsto Kn atTop (𝓝 K) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [norm_sub_rev]
    exact hKn1 n
  -- convergence of the products in `L¹`
  have hPtend : Tendsto (fun n => mulCLM μ (Fn n) (Kn n)) atTop (𝓝 (mulCLM μ F K)) := by
    have hcont : Continuous fun p : Lp ℂ 1 μ × Lp ℂ 1 μ => mulCLM μ p.1 p.2 :=
      (mulCLM μ).isBoundedBilinearMap.continuous
    exact (hcont.tendsto (F, K)).comp (hFtend.prodMk_nhds hKtend)
  -- pass to an a.e. convergent subsequence
  have hmeasconv : TendstoInMeasure μ (fun n => ⇑(mulCLM μ (Fn n) (Kn n))) atTop
      ⇑(mulCLM μ F K) := tendstoInMeasure_of_tendsto_Lp hPtend
  obtain ⟨ns, hns, haeconv⟩ := hmeasconv.exists_seq_tendsto_ae
  have hPn_ae : ∀ n, ⇑(mulCLM μ (Fn n) (Kn n)) =ᵐ[μ] mconv μ (v n) (w n) := by
    intro n
    rw [hFndef, hKndef, mulCLM_toLpCc μ (v n) (w n) (hvc n) (hvs n) (hwc n) (hws n)]
    exact coeFn_toLpCc μ _ _ _
  filter_upwards [haeconv, ae_all_iff.mpr hPn_ae] with x hx1 hx2
  have hx1' : Tendsto (fun i => mconv μ (v (ns i)) (w (ns i)) x) atTop
      (𝓝 (⇑(mulCLM μ F K) x)) := by
    refine hx1.congr fun i => ?_
    exact hx2 (ns i)
  have hx3 : Tendsto (fun i => mconv μ (v (ns i)) (w (ns i)) x) atTop
      (𝓝 (mconv μ f g x)) := (hunif x).comp hns.tendsto_atTop
  exact tendsto_nhds_unique hx3 hx1'

end ConvolutionConsistency

/-! ### The Plancherel identity for continuous compactly supported functions -/

section CcParseval

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- The squared modulus of the transform of a `C_c` function is integrable against the dual
Haar measure. -/
theorem integrable_norm_sq_fourierTransform_cc {v : G → ℂ} (hvc : Continuous v)
    (hvs : HasCompactSupport v) :
    Integrable (fun χ => ‖fourierTransform μ v χ‖ ^ 2) (dualHaar μ) := by
  set φ : G → ℂ := mconv μ v (mstar v) with hφdef
  have hφc : Continuous φ := hvc.mconv μ hvs hvc.mstar hvs.mstar
  have hφs : HasCompactSupport φ := hvs.mconv μ hvs.mstar
  have hφi : Integrable φ μ := hφc.integrable_of_hasCompactSupport hφs
  have hφpt : IsPositiveType φ := isPositiveType_mconv_mstar μ hvc hvs
  obtain ⟨σφ, hfin, hreg, hrep⟩ := hφpt.exists_bochner_measure μ hφc
  haveI := hfin
  haveI := hreg
  have h := integrable_re_fourierTransform_dualHaar μ σφ hφi hrep
  refine h.congr ?_
  refine Eventually.of_forall fun χ => ?_
  show (fourierTransform μ φ χ).re = ‖fourierTransform μ v χ‖ ^ 2
  rw [hφdef, fourierTransform_mconv_mstar μ hvc hvs χ, Complex.ofReal_re]

/-- **The Plancherel identity for `C_c` functions**:
`∫ ‖𝓕v‖² ∂(dualHaar μ) = ∫ ‖v‖² ∂μ`, by Fourier inversion at `1` for the positive-type
convolution square `v ⋆ v^*`. -/
theorem integral_norm_sq_fourierTransform_cc {v : G → ℂ} (hvc : Continuous v)
    (hvs : HasCompactSupport v) :
    ∫ χ, ‖fourierTransform μ v χ‖ ^ 2 ∂(dualHaar μ) = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  set φ : G → ℂ := mconv μ v (mstar v) with hφdef
  have hφc : Continuous φ := hvc.mconv μ hvs hvc.mstar hvs.mstar
  have hφs : HasCompactSupport φ := hvs.mconv μ hvs.mstar
  have hφi : Integrable φ μ := hφc.integrable_of_hasCompactSupport hφs
  have hφpt : IsPositiveType φ := isPositiveType_mconv_mstar μ hvc hvs
  have h1 : φ 1 = ∫ χ, fourierTransform μ φ χ ∂(dualHaar μ) :=
    hφpt.fourier_inversion_one μ hφc hφi
  have h2 : ∫ χ, fourierTransform μ φ χ ∂(dualHaar μ)
      = ((∫ χ, ‖fourierTransform μ v χ‖ ^ 2 ∂(dualHaar μ) : ℝ) : ℂ) := by
    calc ∫ χ, fourierTransform μ φ χ ∂(dualHaar μ)
        = ∫ χ, ((‖fourierTransform μ v χ‖ ^ 2 : ℝ) : ℂ) ∂(dualHaar μ) := by
          refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
          rw [hφdef]
          exact fourierTransform_mconv_mstar μ hvc hvs χ
      _ = ((∫ χ, ‖fourierTransform μ v χ‖ ^ 2 ∂(dualHaar μ) : ℝ) : ℂ) := integral_ofReal
  have h3 : φ 1 = ((∫ x, ‖v x‖ ^ 2 ∂μ : ℝ) : ℂ) := mconv_mstar_self_one μ v
  have h4 : ((∫ x, ‖v x‖ ^ 2 ∂μ : ℝ) : ℂ)
      = ((∫ χ, ‖fourierTransform μ v χ‖ ^ 2 ∂(dualHaar μ) : ℝ) : ℂ) := by
    rw [← h3, h1, h2]
  exact_mod_cast h4.symm

/-- The Fourier transform of a `C_c` function lies in `L²` of the dual Haar measure. -/
theorem memLp_two_fourierTransform_cc {v : G → ℂ} (hvc : Continuous v)
    (hvs : HasCompactSupport v) :
    MemLp (fourierTransform μ v) 2 (dualHaar μ) := by
  have hvi : Integrable v μ := hvc.integrable_of_hasCompactSupport hvs
  have hcont : Continuous (fourierTransform μ v) := continuous_fourierTransform μ hvi
  exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
    (integrable_norm_sq_fourierTransform_cc μ hvc hvs)

end CcParseval

/-! ### The subspace of `C_c` classes in `L²` -/

section CcL2

/-- The `L²` class of a continuous compactly supported function. -/
def toLp2Cc (v : G → ℂ) (hvc : Continuous v) (hvs : HasCompactSupport v) : Lp ℂ 2 μ :=
  (hvc.memLp_of_hasCompactSupport hvs).toLp v

theorem coeFn_toLp2Cc (v : G → ℂ) (hvc : Continuous v) (hvs : HasCompactSupport v) :
    ⇑(toLp2Cc μ v hvc hvs) =ᵐ[μ] v :=
  MemLp.coeFn_toLp _

/-- The subspace of `L²` classes possessing a continuous compactly supported
representative. -/
def ccL2Submodule : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {F | ∃ v : G → ℂ, Continuous v ∧ HasCompactSupport v ∧ ⇑F =ᵐ[μ] v}
  add_mem' := by
    rintro F K ⟨f, hfc, hfs, hf⟩ ⟨k, hkc, hks, hk⟩
    exact ⟨f + k, hfc.add hkc, hfs.add hks, (Lp.coeFn_add F K).trans (hf.add hk)⟩
  zero_mem' := ⟨0, continuous_const, HasCompactSupport.zero, Lp.coeFn_zero ℂ 2 μ⟩
  smul_mem' := by
    rintro c F ⟨f, hfc, hfs, hf⟩
    exact ⟨c • f, hfc.const_smul c, hfs.mono (support_const_smul_subset c f),
      (Lp.coeFn_smul c F).trans (hf.const_smul c)⟩

theorem mem_ccL2Submodule_iff {F : Lp ℂ 2 μ} :
    F ∈ ccL2Submodule μ ↔
      ∃ v : G → ℂ, Continuous v ∧ HasCompactSupport v ∧ ⇑F =ᵐ[μ] v :=
  Iff.rfl

theorem toLp2Cc_mem_ccL2Submodule (v : G → ℂ) (hvc : Continuous v)
    (hvs : HasCompactSupport v) : toLp2Cc μ v hvc hvs ∈ ccL2Submodule μ :=
  ⟨v, hvc, hvs, coeFn_toLp2Cc μ v hvc hvs⟩

/-- **Density of the `C_c` classes in `L²`**, as a submodule. -/
theorem dense_ccL2Submodule : Dense (ccL2Submodule μ : Set (Lp ℂ 2 μ)) :=
  dense_ccL2

theorem denseRange_ccL2SubtypeL : DenseRange ⇑(ccL2Submodule μ).subtypeL :=
  (dense_ccL2Submodule μ).denseRange_val

theorem isUniformInducing_ccL2SubtypeL : IsUniformInducing ⇑(ccL2Submodule μ).subtypeL :=
  isUniformEmbedding_subtype_val.isUniformInducing

/-- A workhorse: two continuous functions on `L²` agreeing on all `C_c` classes are equal. -/
theorem funext_of_denseL2 {X : Type*} [TopologicalSpace X] [T2Space X]
    (T S : Lp ℂ 2 μ → X) (hT : Continuous T) (hS : Continuous S)
    (h : ∀ (v : G → ℂ) (hvc : Continuous v) (hvs : HasCompactSupport v),
      T (toLp2Cc μ v hvc hvs) = S (toLp2Cc μ v hvc hvs)) (F : Lp ℂ 2 μ) :
    T F = S F := by
  have hTS : T = S := by
    refine Continuous.ext_on (dense_ccL2Submodule μ) hT hS ?_
    intro F₀ hF₀
    obtain ⟨v, hvc, hvs, hv⟩ := (mem_ccL2Submodule_iff μ).mp hF₀
    have hrw : F₀ = toLp2Cc μ v hvc hvs := Lp.ext (hv.trans (coeFn_toLp2Cc μ v hvc hvs).symm)
    rw [hrw]
    exact h v hvc hvs
  rw [hTS]

private theorem ccL2_mem_def (F : ccL2Submodule μ) :
    ∃ v : G → ℂ, Continuous v ∧ HasCompactSupport v ∧ ⇑(F : Lp ℂ 2 μ) =ᵐ[μ] v :=
  F.2

/-- A choice of continuous compactly supported representative for an element of
`ccL2Submodule μ`. -/
def ccRep2 (F : ccL2Submodule μ) : G → ℂ :=
  (ccL2_mem_def μ F).choose

theorem ccRep2_continuous (F : ccL2Submodule μ) : Continuous (ccRep2 μ F) :=
  (ccL2_mem_def μ F).choose_spec.1

theorem ccRep2_hasCompactSupport (F : ccL2Submodule μ) :
    HasCompactSupport (ccRep2 μ F) :=
  (ccL2_mem_def μ F).choose_spec.2.1

theorem coeFn_ccRep2 (F : ccL2Submodule μ) : ⇑(F : Lp ℂ 2 μ) =ᵐ[μ] ccRep2 μ F :=
  (ccL2_mem_def μ F).choose_spec.2.2

theorem ccRep2_integrable (F : ccL2Submodule μ) : Integrable (ccRep2 μ F) μ :=
  (ccRep2_continuous μ F).integrable_of_hasCompactSupport (ccRep2_hasCompactSupport μ F)

end CcL2

/-! ### The Plancherel isometry -/

section Plancherel

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- The Plancherel image of a `C_c` class: the `L²(dualHaar μ)` class of the Fourier
transform of the chosen representative. -/
def ccPlancherel (F : ccL2Submodule μ) : Lp ℂ 2 (dualHaar μ) :=
  (memLp_two_fourierTransform_cc μ (ccRep2_continuous μ F)
    (ccRep2_hasCompactSupport μ F)).toLp (fourierTransform μ (ccRep2 μ F))

theorem coeFn_ccPlancherel (F : ccL2Submodule μ) :
    ⇑(ccPlancherel μ F) =ᵐ[dualHaar μ] fourierTransform μ (ccRep2 μ F) :=
  MemLp.coeFn_toLp _

/-- `ccPlancherel` does not depend on the choice of representative. -/
theorem ccPlancherel_eq {F : ccL2Submodule μ} {v : G → ℂ} (hvc : Continuous v)
    (hvs : HasCompactSupport v) (hv : ⇑(F : Lp ℂ 2 μ) =ᵐ[μ] v) :
    ccPlancherel μ F
      = (memLp_two_fourierTransform_cc μ hvc hvs).toLp (fourierTransform μ v) := by
  have hrep : ccRep2 μ F = v :=
    cc_rep_unique μ (ccRep2_continuous μ F) hvc ((coeFn_ccRep2 μ F).symm.trans hv)
  refine Lp.ext ?_
  refine (coeFn_ccPlancherel μ F).trans ?_
  rw [hrep]
  exact (MemLp.coeFn_toLp _).symm

/-- The Plancherel map preserves the norm on `C_c` classes (the `C_c` Parseval identity). -/
theorem norm_ccPlancherel (F : ccL2Submodule μ) : ‖ccPlancherel μ F‖ = ‖F‖ := by
  have hvc := ccRep2_continuous μ F
  have hvs := ccRep2_hasCompactSupport μ F
  have hF : (F : Lp ℂ 2 μ) = toLp2Cc μ (ccRep2 μ F) hvc hvs :=
    Lp.ext ((coeFn_ccRep2 μ F).trans (coeFn_toLp2Cc μ _ hvc hvs).symm)
  rw [Submodule.coe_norm, hF]
  exact norm_toLp_two_eq_of_integral_sq_eq
    (memLp_two_fourierTransform_cc μ hvc hvs) (hvc.memLp_of_hasCompactSupport hvs)
    (integral_norm_sq_fourierTransform_cc μ hvc hvs)

/-- The Plancherel map on the `C_c` subspace, as a linear map. -/
def ccPlancherelₗ : ccL2Submodule μ →ₗ[ℂ] Lp ℂ 2 (dualHaar μ) where
  toFun := ccPlancherel μ
  map_add' F K := by
    have hFi := ccRep2_integrable μ F
    have hKi := ccRep2_integrable μ K
    have hadd : ccRep2 μ (F + K) = ccRep2 μ F + ccRep2 μ K := by
      refine cc_rep_unique μ (ccRep2_continuous μ (F + K))
        ((ccRep2_continuous μ F).add (ccRep2_continuous μ K)) ?_
      refine (coeFn_ccRep2 μ (F + K)).symm.trans ?_
      refine (Lp.coeFn_add (F : Lp ℂ 2 μ) (K : Lp ℂ 2 μ)).trans ?_
      exact (coeFn_ccRep2 μ F).add (coeFn_ccRep2 μ K)
    refine Lp.ext ?_
    have h1 := coeFn_ccPlancherel μ (F + K)
    rw [hadd, fourierTransform_add μ hFi hKi] at h1
    refine h1.trans (EventuallyEq.symm ?_)
    filter_upwards [Lp.coeFn_add (ccPlancherel μ F) (ccPlancherel μ K),
      coeFn_ccPlancherel μ F, coeFn_ccPlancherel μ K] with χ hχ1 hχ2 hχ3
    rw [hχ1, Pi.add_apply, hχ2, hχ3]
    rfl
  map_smul' c F := by
    have hsmul : ccRep2 μ (c • F) = c • ccRep2 μ F := by
      refine cc_rep_unique μ (ccRep2_continuous μ (c • F))
        ((ccRep2_continuous μ F).const_smul c) ?_
      refine (coeFn_ccRep2 μ (c • F)).symm.trans ?_
      refine (Lp.coeFn_smul c (F : Lp ℂ 2 μ)).trans ?_
      exact (coeFn_ccRep2 μ F).const_smul c
    refine Lp.ext ?_
    have h1 := coeFn_ccPlancherel μ (c • F)
    rw [hsmul, fourierTransform_smul μ c (ccRep2 μ F)] at h1
    refine h1.trans (EventuallyEq.symm ?_)
    filter_upwards [Lp.coeFn_smul c (ccPlancherel μ F), coeFn_ccPlancherel μ F]
      with χ hχ1 hχ2
    simp only [RingHom.id_apply]
    rw [hχ1, Pi.smul_apply, hχ2]
    rfl

/-- The Plancherel map on the `C_c` subspace, as a continuous linear map. -/
def ccPlancherelCLM : ccL2Submodule μ →L[ℂ] Lp ℂ 2 (dualHaar μ) :=
  LinearMap.mkContinuous (ccPlancherelₗ μ) 1 fun F => by
    rw [one_mul]
    exact le_of_eq (norm_ccPlancherel μ F)

/-- **The Plancherel transform** `Lp ℂ 2 μ →L Lp ℂ 2 (dualHaar μ)`, obtained by extending
the `C_c`-level Fourier transform along the dense inclusion of the `C_c` classes. -/
def plancherelCLM : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (dualHaar μ) :=
  (ccPlancherelCLM μ).extend (ccL2Submodule μ).subtypeL

theorem plancherelCLM_coe (F : ccL2Submodule μ) :
    plancherelCLM μ (F : Lp ℂ 2 μ) = ccPlancherel μ F :=
  (ccPlancherelCLM μ).extend_eq (denseRange_ccL2SubtypeL μ)
    (isUniformInducing_ccL2SubtypeL μ) F

/-- The Plancherel transform is norm-preserving. -/
theorem norm_plancherelCLM (F : Lp ℂ 2 μ) : ‖plancherelCLM μ F‖ = ‖F‖ := by
  refine funext_of_denseL2 μ (fun F => ‖plancherelCLM μ F‖) (fun F => ‖F‖)
    ((plancherelCLM μ).continuous.norm) continuous_norm ?_ F
  intro v hvc hvs
  have hmem : toLp2Cc μ v hvc hvs ∈ ccL2Submodule μ :=
    toLp2Cc_mem_ccL2Submodule μ v hvc hvs
  have h1 : plancherelCLM μ (toLp2Cc μ v hvc hvs)
      = ccPlancherel μ ⟨toLp2Cc μ v hvc hvs, hmem⟩ :=
    plancherelCLM_coe μ ⟨toLp2Cc μ v hvc hvs, hmem⟩
  rw [h1, norm_ccPlancherel μ ⟨toLp2Cc μ v hvc hvs, hmem⟩]
  rfl

/-- **The Plancherel isometry** `Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 (dualHaar μ)`. -/
def plancherelLI : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 (dualHaar μ) :=
  ⟨(plancherelCLM μ).toLinearMap, norm_plancherelCLM μ⟩

@[simp]
theorem plancherelLI_apply (F : Lp ℂ 2 μ) : plancherelLI μ F = plancherelCLM μ F := rfl

/-- **Agreement on `C_c` classes**: the Plancherel isometry of a `C_c` class is the class of
the pointwise Fourier transform of the representative. -/
theorem plancherelLI_toLp2Cc (v : G → ℂ) (hvc : Continuous v) (hvs : HasCompactSupport v) :
    plancherelLI μ (toLp2Cc μ v hvc hvs)
      = (memLp_two_fourierTransform_cc μ hvc hvs).toLp (fourierTransform μ v) := by
  have hmem : toLp2Cc μ v hvc hvs ∈ ccL2Submodule μ :=
    toLp2Cc_mem_ccL2Submodule μ v hvc hvs
  have h1 : plancherelLI μ (toLp2Cc μ v hvc hvs)
      = ccPlancherel μ ⟨toLp2Cc μ v hvc hvs, hmem⟩ :=
    plancherelCLM_coe μ ⟨toLp2Cc μ v hvc hvs, hmem⟩
  rw [h1]
  exact ccPlancherel_eq μ hvc hvs (coeFn_toLp2Cc μ v hvc hvs)

end Plancherel

/-! ### Parseval's identity on `L¹ ∩ L²` -/

section Parseval

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- Master lemma: the Plancherel image of the `L²` class of `f ∈ L¹ ∩ L²` has the pointwise
Fourier transform `𝓕f` as an a.e. representative. -/
private theorem coeFn_plancherelLI_toLp {f : G → ℂ} (hf1 : Integrable f μ)
    (hf2 : MemLp f 2 μ) :
    ⇑(plancherelLI μ (hf2.toLp f)) =ᵐ[dualHaar μ] fourierTransform μ f := by
  -- simultaneous `C_c` approximations
  have hv' : ∀ n : ℕ, ∃ v : G → ℂ, Continuous v ∧ HasCompactSupport v ∧
      (∫ x, ‖f x - v x‖ ∂μ) ≤ 1 / (n + 1) ∧
      eLpNorm (fun x => f x - v x) 2 μ ≤ ENNReal.ofReal (1 / (n + 1)) := fun n =>
    exists_cc_close_L1_L2 μ hf1 hf2 (by positivity)
  choose v hvc hvs hv1 hv2 using hv'
  have hone : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  set Vn : ℕ → Lp ℂ 2 μ := fun n => toLp2Cc μ (v n) (hvc n) (hvs n) with hVndef
  -- `L²` convergence of the classes
  have hVn : ∀ n, ‖Vn n - hf2.toLp f‖ ≤ 1 / (n + 1) := by
    intro n
    have hae : ⇑(Vn n - hf2.toLp f) =ᵐ[μ] fun x => v n x - f x := by
      filter_upwards [Lp.coeFn_sub (Vn n) (hf2.toLp f),
        coeFn_toLp2Cc μ (v n) (hvc n) (hvs n), hf2.coeFn_toLp] with x hx1 hx2 hx3
      rw [hx1, Pi.sub_apply, hx2, hx3]
    have h1 : eLpNorm (fun x => v n x - f x) 2 μ
        = eLpNorm (fun x => f x - v n x) 2 μ :=
      eLpNorm_congr_norm_ae (Eventually.of_forall fun x => norm_sub_rev _ _)
    calc ‖Vn n - hf2.toLp f‖
        = (eLpNorm (⇑(Vn n - hf2.toLp f)) 2 μ).toReal := by rw [Lp.norm_def]
      _ = (eLpNorm (fun x => f x - v n x) 2 μ).toReal := by
          rw [eLpNorm_congr_ae hae, h1]
      _ ≤ (ENNReal.ofReal (1 / (n + 1))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hv2 n)
      _ = 1 / (n + 1) := ENNReal.toReal_ofReal (hone n).le
  have hVtend : Tendsto Vn atTop (𝓝 (hf2.toLp f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hVn n)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  -- convergence of the Plancherel images
  have hHtend : Tendsto (fun n => plancherelLI μ (Vn n)) atTop
      (𝓝 (plancherelLI μ (hf2.toLp f))) :=
    ((plancherelLI μ).continuous.tendsto _).comp hVtend
  have hmeasconv : TendstoInMeasure (dualHaar μ) (fun n => ⇑(plancherelLI μ (Vn n)))
      atTop ⇑(plancherelLI μ (hf2.toLp f)) := tendstoInMeasure_of_tendsto_Lp hHtend
  obtain ⟨ns, hns, haeconv⟩ := hmeasconv.exists_seq_tendsto_ae
  -- identify the images of `C_c` classes
  have hcc : ∀ n, ⇑(plancherelLI μ (Vn n)) =ᵐ[dualHaar μ] fourierTransform μ (v n) := by
    intro n
    rw [hVndef]
    show ⇑(plancherelLI μ (toLp2Cc μ (v n) (hvc n) (hvs n))) =ᵐ[dualHaar μ] _
    rw [plancherelLI_toLp2Cc μ (v n) (hvc n) (hvs n)]
    exact MemLp.coeFn_toLp _
  -- everywhere convergence of the pointwise transforms
  have hpt : ∀ χ, Tendsto (fun n => fourierTransform μ (v n) χ) atTop
      (𝓝 (fourierTransform μ f χ)) := by
    intro χ
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hvint : Integrable (v n) μ :=
      (hvc n).integrable_of_hasCompactSupport (hvs n)
    calc ‖fourierTransform μ (v n) χ - fourierTransform μ f χ‖
        ≤ ∫ x, ‖v n x - f x‖ ∂μ := norm_fourierTransform_sub_le μ hvint hf1 χ
      _ = ∫ x, ‖f x - v n x‖ ∂μ :=
          integral_congr_ae (Eventually.of_forall fun x => norm_sub_rev _ _)
      _ ≤ 1 / (n + 1) := hv1 n
  -- combine
  filter_upwards [haeconv, ae_all_iff.mpr hcc] with χ hχ1 hχ2
  have hχ1' : Tendsto (fun i => fourierTransform μ (v (ns i)) χ) atTop
      (𝓝 (⇑(plancherelLI μ (hf2.toLp f)) χ)) := by
    refine hχ1.congr fun i => ?_
    exact hχ2 (ns i)
  have hχ3 : Tendsto (fun i => fourierTransform μ (v (ns i)) χ) atTop
      (𝓝 (fourierTransform μ f χ)) := (hpt χ).comp hns.tendsto_atTop
  exact tendsto_nhds_unique hχ1' hχ3

/-- For `f ∈ L¹ ∩ L²`, the Fourier transform lies in `L²` of the dual Haar measure. -/
theorem memLp_two_fourierTransform {f : G → ℂ} (hf1 : Integrable f μ)
    (hf2 : MemLp f 2 μ) : MemLp (fourierTransform μ f) 2 (dualHaar μ) :=
  (Lp.memLp (plancherelLI μ (hf2.toLp f))).ae_eq (coeFn_plancherelLI_toLp μ hf1 hf2)

/-- **Agreement on `L¹ ∩ L²`**: the Plancherel isometry of the class of `f ∈ L¹ ∩ L²` is the
class of the pointwise Fourier transform. -/
theorem plancherelLI_memLp_toLp {f : G → ℂ} (hf1 : Integrable f μ) (hf2 : MemLp f 2 μ) :
    plancherelLI μ (hf2.toLp f)
      = (memLp_two_fourierTransform μ hf1 hf2).toLp (fourierTransform μ f) :=
  Lp.ext ((coeFn_plancherelLI_toLp μ hf1 hf2).trans (MemLp.coeFn_toLp _).symm)

/-- **Parseval's identity**: for `f ∈ L¹ ∩ L²`,
`∫ ‖𝓕f‖² ∂(dualHaar μ) = ∫ ‖f‖² ∂μ`. -/
theorem integral_norm_sq_fourierTransform {f : G → ℂ} (hf1 : Integrable f μ)
    (hf2 : MemLp f 2 μ) :
    ∫ χ, ‖fourierTransform μ f χ‖ ^ 2 ∂(dualHaar μ) = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  calc ∫ χ, ‖fourierTransform μ f χ‖ ^ 2 ∂(dualHaar μ)
      = ‖(memLp_two_fourierTransform μ hf1 hf2).toLp (fourierTransform μ f)‖ ^ 2 :=
        (norm_toLp_two_sq (memLp_two_fourierTransform μ hf1 hf2)).symm
    _ = ‖plancherelLI μ (hf2.toLp f)‖ ^ 2 := by rw [plancherelLI_memLp_toLp μ hf1 hf2]
    _ = ‖hf2.toLp f‖ ^ 2 := by rw [(plancherelLI μ).norm_map]
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := norm_toLp_two_sq hf2

end Parseval

/-! ### Uniqueness for integrable densities on the dual -/

section DualUniqueness

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- Joint continuity of character evaluation (local copy of the Fubini kernel helper). -/
private theorem continuous_char_eval' :
    Continuous fun p : PontryaginDual G × G => ((p.1 p.2 : Circle) : ℂ) := by
  change Continuous fun p : (G →ₜ* Circle) × G => ((p.1 p.2 : Circle) : ℂ)
  exact continuous_induced_dom.comp continuous_eval

/-- Fubini for a `C_c` transform against a `C_c` density on the dual group. -/
private theorem integral_fourier_mul_cc_dual {u : PontryaginDual G → ℂ}
    (huc : Continuous u) (hus : HasCompactSupport u)
    {f : G → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f) :
    ∫ χ, fourierTransform μ f χ * u χ ∂(dualHaar μ)
      = ∫ y, f y * ∫ χ, conj ((χ y : Circle) : ℂ) * u χ ∂(dualHaar μ) ∂μ := by
  have hFc : Continuous (uncurry fun (χ : PontryaginDual G) (y : G) =>
      f y * conj ((χ y : Circle) : ℂ) * u χ) :=
    ((hfc.comp continuous_snd).mul
      (Complex.continuous_conj.comp (continuous_char_eval' (G := G)))).mul
      (huc.comp continuous_fst)
  have hFs : HasCompactSupport (uncurry fun (χ : PontryaginDual G) (y : G) =>
      f y * conj ((χ y : Circle) : ℂ) * u χ) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (hus.isCompact.prod hfs.isCompact) ?_
    rintro ⟨χ, y⟩ hp
    have hp' : f y * conj ((χ y : Circle) : ℂ) * u χ ≠ 0 := hp
    refine Set.mem_prod.mpr ⟨?_, ?_⟩
    · exact subset_tsupport u (mem_support.mpr (right_ne_zero_of_mul hp'))
    · exact subset_tsupport f (mem_support.mpr
        (left_ne_zero_of_mul (left_ne_zero_of_mul hp')))
  calc ∫ χ, fourierTransform μ f χ * u χ ∂(dualHaar μ)
      = ∫ χ, ∫ y, f y * conj ((χ y : Circle) : ℂ) * u χ ∂μ ∂(dualHaar μ) := by
        refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
        show fourierTransform μ f χ * u χ = _
        rw [fourierTransform_apply, ← integral_mul_const]
    _ = ∫ y, ∫ χ, f y * conj ((χ y : Circle) : ℂ) * u χ ∂(dualHaar μ) ∂μ :=
        integral_integral_swap_of_continuous_compactSupport hFc hFs
    _ = ∫ y, f y * ∫ χ, conj ((χ y : Circle) : ℂ) * u χ ∂(dualHaar μ) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        show ∫ χ, f y * conj ((χ y : Circle) : ℂ) * u χ ∂(dualHaar μ)
          = f y * ∫ χ, conj ((χ y : Circle) : ℂ) * u χ ∂(dualHaar μ)
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
        ring

/-- If all "inverse Fourier coefficients" of an integrable density `w` on the dual vanish,
then `w` integrates all `C_c` Fourier transforms to zero. -/
private theorem integral_fourierTransform_mul_eq_zero {w : PontryaginDual G → ℂ}
    (hw : Integrable w (dualHaar μ))
    (h : ∀ x : G, ∫ χ, (χ x : ℂ) * w χ ∂(dualHaar μ) = 0)
    {f : G → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f) :
    ∫ χ, fourierTransform μ f χ * w χ ∂(dualHaar μ) = 0 := by
  set Cf : ℝ := ∫ x, ‖f x‖ ∂μ with hCfdef
  have hCf0 : 0 ≤ Cf := integral_nonneg fun x => norm_nonneg _
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hFTc : Continuous (fourierTransform μ f) := continuous_fourierTransform μ hfi
  have hIfw : Integrable (fun χ => fourierTransform μ f χ * w χ) (dualHaar μ) :=
    hw.bdd_mul hFTc.aestronglyMeasurable
      (Eventually.of_forall fun χ => norm_fourierTransform_le μ f χ)
  have key : ∀ δ : ℝ, 0 < δ →
      ‖∫ χ, fourierTransform μ f χ * w χ ∂(dualHaar μ)‖ ≤ δ * (2 * Cf) := by
    intro δ hδ
    obtain ⟨u, huc, hus, hui, huclose⟩ :=
      exists_hasCompactSupport_integral_norm_sub_le hw hδ
    have hIfu : Integrable (fun χ => fourierTransform μ f χ * u χ) (dualHaar μ) :=
      hui.bdd_mul hFTc.aestronglyMeasurable
        (Eventually.of_forall fun χ => norm_fourierTransform_le μ f χ)
    -- replacing `w` by `u` costs at most `Cf * δ`
    have h1 : ‖(∫ χ, fourierTransform μ f χ * w χ ∂(dualHaar μ))
        - ∫ χ, fourierTransform μ f χ * u χ ∂(dualHaar μ)‖ ≤ Cf * δ := by
      rw [← integral_sub hIfw hIfu]
      calc ‖∫ χ, (fourierTransform μ f χ * w χ - fourierTransform μ f χ * u χ)
              ∂(dualHaar μ)‖
          ≤ ∫ χ, Cf * ‖w χ - u χ‖ ∂(dualHaar μ) := by
            refine norm_integral_le_of_norm_le ((hw.sub hui).norm.const_mul Cf)
              (Eventually.of_forall fun χ => ?_)
            calc ‖fourierTransform μ f χ * w χ - fourierTransform μ f χ * u χ‖
                = ‖fourierTransform μ f χ‖ * ‖w χ - u χ‖ := by rw [← mul_sub, norm_mul]
              _ ≤ Cf * ‖w χ - u χ‖ := mul_le_mul_of_nonneg_right
                  (norm_fourierTransform_le μ f χ) (norm_nonneg _)
        _ = Cf * ∫ χ, ‖w χ - u χ‖ ∂(dualHaar μ) := integral_const_mul _ _
        _ ≤ Cf * δ := mul_le_mul_of_nonneg_left huclose hCf0
    -- the inner integrals against `u` are uniformly small
    have hIner : ∀ y : G, ‖∫ χ, conj ((χ y : Circle) : ℂ) * u χ ∂(dualHaar μ)‖ ≤ δ := by
      intro y
      have hchar : Continuous fun χ : PontryaginDual G => conj ((χ y : Circle) : ℂ) :=
        Complex.continuous_conj.comp (continuous_char_apply y)
      have hIu : Integrable (fun χ => conj ((χ y : Circle) : ℂ) * u χ) (dualHaar μ) :=
        hui.bdd_mul hchar.aestronglyMeasurable
          (Eventually.of_forall fun χ => by rw [RCLike.norm_conj, Circle.norm_coe])
      have hIw : Integrable (fun χ => conj ((χ y : Circle) : ℂ) * w χ) (dualHaar μ) :=
        hw.bdd_mul hchar.aestronglyMeasurable
          (Eventually.of_forall fun χ => by rw [RCLike.norm_conj, Circle.norm_coe])
      have hw0 : ∫ χ, conj ((χ y : Circle) : ℂ) * w χ ∂(dualHaar μ) = 0 := by
        rw [show (fun χ : PontryaginDual G => conj ((χ y : Circle) : ℂ) * w χ)
            = fun χ : PontryaginDual G => ((χ y⁻¹ : Circle) : ℂ) * w χ from
          funext fun χ => by rw [conj_char_apply]]
        exact h y⁻¹
      calc ‖∫ χ, conj ((χ y : Circle) : ℂ) * u χ ∂(dualHaar μ)‖
          = ‖(∫ χ, conj ((χ y : Circle) : ℂ) * u χ ∂(dualHaar μ))
              - ∫ χ, conj ((χ y : Circle) : ℂ) * w χ ∂(dualHaar μ)‖ := by
            rw [hw0, sub_zero]
        _ = ‖∫ χ, (conj ((χ y : Circle) : ℂ) * u χ
              - conj ((χ y : Circle) : ℂ) * w χ) ∂(dualHaar μ)‖ := by
            rw [integral_sub hIu hIw]
        _ ≤ ∫ χ, ‖w χ - u χ‖ ∂(dualHaar μ) := by
            refine norm_integral_le_of_norm_le (hw.sub hui).norm
              (Eventually.of_forall fun χ => ?_)
            calc ‖conj ((χ y : Circle) : ℂ) * u χ - conj ((χ y : Circle) : ℂ) * w χ‖
                = ‖conj ((χ y : Circle) : ℂ)‖ * ‖u χ - w χ‖ := by
                  rw [← mul_sub, norm_mul]
              _ = ‖u χ - w χ‖ := by rw [RCLike.norm_conj, Circle.norm_coe, one_mul]
              _ = ‖w χ - u χ‖ := norm_sub_rev _ _
              _ ≤ ‖w χ - u χ‖ := le_rfl
        _ ≤ δ := huclose
    -- the integral against `u` is at most `Cf * δ`
    have h2 : ‖∫ χ, fourierTransform μ f χ * u χ ∂(dualHaar μ)‖ ≤ Cf * δ := by
      rw [integral_fourier_mul_cc_dual μ huc hus hfc hfs]
      calc ‖∫ y, f y * ∫ χ, conj ((χ y : Circle) : ℂ) * u χ ∂(dualHaar μ) ∂μ‖
          ≤ ∫ y, ‖f y‖ * δ ∂μ := by
            refine norm_integral_le_of_norm_le (hfi.norm.mul_const δ)
              (Eventually.of_forall fun y => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hIner y) (norm_nonneg _)
        _ = Cf * δ := by rw [integral_mul_const]
    calc ‖∫ χ, fourierTransform μ f χ * w χ ∂(dualHaar μ)‖
        = ‖((∫ χ, fourierTransform μ f χ * w χ ∂(dualHaar μ))
              - ∫ χ, fourierTransform μ f χ * u χ ∂(dualHaar μ))
            + ∫ χ, fourierTransform μ f χ * u χ ∂(dualHaar μ)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖(∫ χ, fourierTransform μ f χ * w χ ∂(dualHaar μ))
              - ∫ χ, fourierTransform μ f χ * u χ ∂(dualHaar μ)‖
            + ‖∫ χ, fourierTransform μ f χ * u χ ∂(dualHaar μ)‖ := norm_add_le _ _
      _ ≤ Cf * δ + Cf * δ := add_le_add h1 h2
      _ = δ * (2 * Cf) := by ring
  have h0 : ‖∫ χ, fourierTransform μ f χ * w χ ∂(dualHaar μ)‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hδ : 0 < ε / (2 * Cf + 1) := by positivity
    refine (key _ hδ).trans ?_
    have h3 : ε / (2 * Cf + 1) * (2 * Cf) ≤ ε / (2 * Cf + 1) * (2 * Cf + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ.le
    rw [div_mul_cancel₀ ε (by positivity : (2 * Cf + 1 : ℝ) ≠ 0)] at h3
    linarith
  exact sub_eq_zero.mp (by simpa using norm_le_zero_iff.mp h0)

/-- Integration against an integrable density on the dual is continuous on `C₀`. -/
private theorem continuous_integral_c0_mul_integrable {w : PontryaginDual G → ℂ}
    (hw : Integrable w (dualHaar μ)) :
    Continuous fun b : C₀(PontryaginDual G, ℂ) => ∫ χ, b χ * w χ ∂(dualHaar μ) := by
  set I : ℝ := ∫ χ, ‖w χ‖ ∂(dualHaar μ) with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun χ => norm_nonneg _
  have hint : ∀ b : C₀(PontryaginDual G, ℂ),
      Integrable (fun χ => b χ * w χ) (dualHaar μ) := fun b =>
    hw.bdd_mul (map_continuous b).aestronglyMeasurable
      (Eventually.of_forall b.norm_apply_le)
  refine (LipschitzWith.of_dist_le_mul (K := I.toNNReal) fun b b' => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : (∫ χ, b χ * w χ ∂(dualHaar μ)) - ∫ χ, b' χ * w χ ∂(dualHaar μ)
      = ∫ χ, (b - b') χ * w χ ∂(dualHaar μ) := by
    rw [← integral_sub (hint b) (hint b')]
    refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
    show b χ * w χ - b' χ * w χ = (b - b') χ * w χ
    rw [ZeroAtInftyContinuousMap.sub_apply]
    ring
  rw [hsub]
  calc ‖∫ χ, (b - b') χ * w χ ∂(dualHaar μ)‖
      ≤ ∫ χ, ‖b - b'‖ * ‖w χ‖ ∂(dualHaar μ) := by
        refine norm_integral_le_of_norm_le (hw.norm.const_mul _)
          (Eventually.of_forall fun χ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right ((b - b').norm_apply_le χ) (norm_nonneg _)
    _ = ‖b - b'‖ * I := integral_const_mul _ _
    _ ≤ (I.toNNReal : ℝ) * ‖b - b'‖ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal I) (norm_nonneg _)

/-- Extension of `integral_fourierTransform_mul_eq_zero` from `C_c` transforms to all of
`C₀(Ĝ, ℂ)`, by Stone–Weierstrass density. -/
private theorem integral_c0_mul_eq_zero_of_forall_char {w : PontryaginDual G → ℂ}
    (hw : Integrable w (dualHaar μ))
    (h : ∀ x : G, ∫ χ, (χ x : ℂ) * w χ ∂(dualHaar μ) = 0)
    (b : C₀(PontryaginDual G, ℂ)) :
    ∫ χ, b χ * w χ ∂(dualHaar μ) = 0 := by
  have hEqOn : Set.EqOn
      (fun b : C₀(PontryaginDual G, ℂ) => ∫ χ, b χ * w χ ∂(dualHaar μ))
      (fun _ => (0 : ℂ)) (ccFourierSubalgebra μ : Set C₀(PontryaginDual G, ℂ)) := by
    rintro _ ⟨g, hgc, hgs, rfl⟩
    show ∫ χ, fourierTransform μ g χ * w χ ∂(dualHaar μ) = 0
    exact integral_fourierTransform_mul_eq_zero μ hw h hgc hgs
  have hfun : (fun b : C₀(PontryaginDual G, ℂ) => ∫ χ, b χ * w χ ∂(dualHaar μ))
      = fun _ => (0 : ℂ) :=
    Continuous.ext_on (dense_ccFourierSubalgebra μ)
      (continuous_integral_c0_mul_integrable μ hw) continuous_const hEqOn
  exact congrFun hfun b

/-- **Uniqueness for integrable densities on the dual.**  If `w ∈ L¹(dualHaar μ)` satisfies
`∫ χ, χ(x) ⬝ w(χ) ∂(dualHaar μ) = 0` for every `x : G`, then `w = 0` almost everywhere. -/
theorem ae_eq_zero_of_forall_integral_char_mul_eq_zero {w : PontryaginDual G → ℂ}
    (hw : Integrable w (dualHaar μ))
    (h : ∀ x : G, ∫ χ, (χ x : ℂ) * w χ ∂(dualHaar μ) = 0) :
    w =ᵐ[dualHaar μ] 0 := by
  refine ae_eq_zero_of_forall_integral_mul_eq_zero hw fun φ hφc hφs => ?_
  set b : C₀(PontryaginDual G, ℂ) := ⟨⟨φ, hφc⟩, hφs.is_zero_at_infty⟩ with hbdef
  have h0 := integral_c0_mul_eq_zero_of_forall_char μ hw h b
  calc ∫ χ, w χ * φ χ ∂(dualHaar μ)
      = ∫ χ, b χ * w χ ∂(dualHaar μ) := by
        refine integral_congr_ae (Eventually.of_forall fun χ => ?_)
        show w χ * φ χ = φ χ * w χ
        ring
    _ = 0 := h0

end DualUniqueness

/-! ### Surjectivity of the Plancherel isometry -/

section Surjectivity

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

set_option maxHeartbeats 800000 in
-- A long proof: orthogonal complement, admissible squares and inner regularity in one go.
/-- **Surjectivity of the Plancherel isometry.**  The range is closed (isometric image of a
complete space); its orthogonal complement vanishes: an orthogonal vector `H` pairs to zero
with all transforms of translates of `C_c` functions, so the densities `conj (𝓕v) ⬝ H` have
vanishing inverse Fourier coefficients, hence vanish a.e.; admissible squares make `𝓕v`
nonvanishing on any given compact set, so `H = 0` by inner regularity. -/
theorem surjective_plancherelLI : Function.Surjective ⇑(plancherelLI μ) := by
  set Rng : Submodule ℂ (Lp ℂ 2 (dualHaar μ)) :=
    LinearMap.range (plancherelLI μ).toLinearMap with hRdef
  -- the range is closed
  have hclosed : IsClosed (Rng : Set (Lp ℂ 2 (dualHaar μ))) := by
    have h1 : (Rng : Set (Lp ℂ 2 (dualHaar μ))) = Set.range ⇑(plancherelLI μ) := by
      rw [hRdef]
      exact LinearMap.coe_range _
    rw [h1]
    exact ((plancherelLI μ).isometry.isClosedEmbedding).isClosed_range
  -- the orthogonal complement is trivial
  have horth : Rngᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro H hH
    -- for every `C_c` function `v`, the density `conj (𝓕v) ⬝ H` is a.e. zero
    have hkey : ∀ (v : G → ℂ), Continuous v → HasCompactSupport v →
        (fun χ => conj (fourierTransform μ v χ) * ⇑H χ) =ᵐ[dualHaar μ] 0 := by
      intro v hvc hvs
      have hFv2 : MemLp (fourierTransform μ v) 2 (dualHaar μ) :=
        memLp_two_fourierTransform_cc μ hvc hvs
      have hconj2 : MemLp (fun χ => conj (fourierTransform μ v χ)) 2 (dualHaar μ) := by
        refine hFv2.star.ae_eq (Eventually.of_forall fun χ => ?_)
        rw [Pi.star_apply, RCLike.star_def]
      have hwint : Integrable (fun χ => conj (fourierTransform μ v χ) * ⇑H χ)
          (dualHaar μ) := hconj2.integrable_mul (Lp.memLp H)
      refine ae_eq_zero_of_forall_integral_char_mul_eq_zero μ hwint fun x => ?_
      have htr_c : Continuous (mtranslate x v) := hvc.mtranslate x
      have htr_s : HasCompactSupport (mtranslate x v) := hvs.mtranslate x
      have hmem : plancherelLI μ (toLp2Cc μ (mtranslate x v) htr_c htr_s) ∈ Rng :=
        ⟨toLp2Cc μ (mtranslate x v) htr_c htr_s, rfl⟩
      have hzero : inner ℂ (plancherelLI μ (toLp2Cc μ (mtranslate x v) htr_c htr_s)) H
          = 0 := (Submodule.mem_orthogonal Rng H).mp hH _ hmem
      have hid : inner ℂ (plancherelLI μ (toLp2Cc μ (mtranslate x v) htr_c htr_s)) H
          = ∫ χ, (χ x : ℂ) * (conj (fourierTransform μ v χ) * ⇑H χ) ∂(dualHaar μ) := by
        rw [plancherelLI_toLp2Cc μ (mtranslate x v) htr_c htr_s, L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_two_fourierTransform_cc μ htr_c htr_s)]
          with χ hχ
        rw [RCLike.inner_apply, hχ, fourierTransform_mtranslate μ v x χ, map_mul,
          RCLike.conj_conj]
        ring
      rw [← hid]
      exact hzero
    -- `H` vanishes a.e. on every compact set of characters
    have hQ : ∀ Q : Set (PontryaginDual G), IsCompact Q →
        ∀ᵐ χ ∂(dualHaar μ), χ ∈ Q → ⇑H χ = 0 := by
      intro Q hQc
      obtain ⟨E⟩ := exists_admissibleSquare μ hQc
      filter_upwards [hkey E.e (E.cont) (E.supp)] with χ hχ hχQ
      have hne : fourierTransform μ E.e χ ≠ 0 := E.transform_ne_zero μ hχQ
      have hχ' : conj (fourierTransform μ E.e χ) * ⇑H χ = 0 := by simpa using hχ
      rcases mul_eq_zero.mp hχ' with h1 | h1
      · rw [starRingEnd_apply] at h1
        exact absurd (star_eq_zero.mp h1) hne
      · exact h1
    -- pass from compact sets to the whole space via inner regularity
    have hH2 : MemLp (⇑H) 2 (dualHaar μ) := Lp.memLp H
    set H' : PontryaginDual G → ℂ := hH2.1.mk ⇑H with hH'def
    have hH'sm : StronglyMeasurable H' := hH2.1.stronglyMeasurable_mk
    have hHH' : ⇑H =ᵐ[dualHaar μ] H' := hH2.1.ae_eq_mk
    have hH'2 : MemLp H' 2 (dualHaar μ) := hH2.ae_eq hHH'
    have hH'sq : Integrable (fun χ => ‖H' χ‖ ^ 2) (dualHaar μ) :=
      (memLp_two_iff_integrable_sq_norm hH'2.1).mp hH'2
    set S : ℕ → Set (PontryaginDual G) := fun n => {χ | 1 / (n + 1 : ℝ) < ‖H' χ‖}
      with hSdef
    have hSmeas : ∀ n, MeasurableSet (S n) := fun n =>
      measurableSet_lt measurable_const hH'sm.measurable.norm
    have hSfin : ∀ n, (dualHaar μ) (S n) < ∞ := by
      intro n
      have h2 : (0 : ℝ) < 1 / (n + 1) := by positivity
      have h1 : S n ⊆ {χ | (1 / (n + 1 : ℝ)) ^ 2 < ‖H' χ‖ ^ 2} := by
        intro χ hχ
        have hχ' : 1 / (n + 1 : ℝ) < ‖H' χ‖ := hχ
        show (1 / (n + 1 : ℝ)) ^ 2 < ‖H' χ‖ ^ 2
        nlinarith [norm_nonneg (H' χ)]
      exact lt_of_le_of_lt (measure_mono h1) (hH'sq.measure_gt_lt_top (by positivity))
    have hSnull : ∀ n, (dualHaar μ) (S n) = 0 := by
      intro n
      by_contra hne
      have hhalf : (dualHaar μ) (S n) / 2 ≠ 0 := by
        intro h0
        rcases ENNReal.div_eq_zero_iff.mp h0 with h1 | h1
        · exact hne h1
        · exact absurd h1 (by norm_num)
      obtain ⟨Q, hQsub, hQcomp, hQlt⟩ :=
        (hSmeas n).exists_isCompact_lt_add (hSfin n).ne hhalf
      have hQ0 : (dualHaar μ) Q ≠ 0 := by
        intro h0
        rw [h0, zero_add] at hQlt
        exact absurd hQlt (not_lt.mpr ENNReal.half_le_self)
      refine hQ0 ?_
      have h2 : ∀ᵐ χ ∂(dualHaar μ), χ ∉ Q := by
        filter_upwards [hQ Q hQcomp, hHH'] with χ hχ1 hχ2
        intro hχQ
        have h3 : ⇑H χ = 0 := hχ1 hχQ
        have h4 : 1 / (n + 1 : ℝ) < ‖H' χ‖ := hQsub hχQ
        rw [← hχ2, h3, norm_zero] at h4
        have h5 : (0 : ℝ) < 1 / (n + 1) := by positivity
        linarith
      exact measure_eq_zero_iff_ae_notMem.mpr h2
    have hunion : ∀ᵐ χ ∂(dualHaar μ), χ ∉ ⋃ n, S n :=
      measure_eq_zero_iff_ae_notMem.mp (measure_iUnion_null hSnull)
    have hH0 : ⇑H =ᵐ[dualHaar μ] 0 := by
      filter_upwards [hunion, hHH'] with χ hχ1 hχ2
      show ⇑H χ = 0
      by_contra hne
      have h1 : 0 < ‖H' χ‖ := by
        rw [← hχ2]
        exact norm_pos_iff.mpr hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt h1
      exact hχ1 (Set.mem_iUnion.mpr ⟨n, hn⟩)
    exact Lp.ext (hH0.trans (Lp.coeFn_zero ℂ 2 (dualHaar μ)).symm)
  -- closed with dense range: the range is everything
  have htop : Rng = ⊤ := by
    have h1 : Rng.topologicalClosure = ⊤ :=
      Submodule.topologicalClosure_eq_top_iff.mpr horth
    rw [← h1, IsClosed.submodule_topologicalClosure_eq hclosed]
  intro Y
  have hY : Y ∈ Rng := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨F, hF⟩ := hY
  exact ⟨F, hF⟩

end Surjectivity

/-! ### Localized Fourier transforms -/

section Localized

variable [mΓ : MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- Conjugate-modulation under the Fourier transform:
`𝓕(conj v ⬝ η)(χ) = conj (𝓕v (χ⁻¹ ⬝ η))`. -/
theorem fourierTransform_conj_mul_char (v : G → ℂ) (η χ : PontryaginDual G) :
    fourierTransform μ (fun x => conj (v x) * ((η x : Circle) : ℂ)) χ
      = conj (fourierTransform μ v (χ⁻¹ * η)) := by
  rw [fourierTransform_apply, fourierTransform_apply, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show conj (v x) * ((η x : Circle) : ℂ) * conj ((χ x : Circle) : ℂ)
    = conj (v x * conj (((χ⁻¹ * η) x : Circle) : ℂ))
  have h1 : (((χ⁻¹ * η) x : Circle) : ℂ)
      = conj ((χ x : Circle) : ℂ) * ((η x : Circle) : ℂ) := by
    rw [show (χ⁻¹ * η) x = (χ x)⁻¹ * η x from rfl, Circle.coe_mul, Circle.coe_inv_eq_conj]
  have h2 : conj (v x * conj (((χ⁻¹ * η) x : Circle) : ℂ))
      = conj (v x) * (((χ⁻¹ * η) x : Circle) : ℂ) := by
    rw [map_mul, RCLike.conj_conj]
  rw [h2, h1]
  ring

/-- Multiplying (the conjugate of) an `L²` class by a character, as an operation on `L²`. -/
private theorem memLp_conj_mul_char (F : Lp ℂ 2 μ) (η : PontryaginDual G) :
    MemLp (fun x => conj ((F : G → ℂ) x) * ((η x : Circle) : ℂ)) 2 μ := by
  refine MemLp.of_le (Lp.memLp F)
    ((Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable F)).mul
      (continuous_induced_dom.comp (map_continuous η)).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  calc ‖conj ((F : G → ℂ) x) * ((η x : Circle) : ℂ)‖
      = ‖(F : G → ℂ) x‖ := by rw [norm_mul, RCLike.norm_conj, Circle.norm_coe, mul_one]
    _ ≤ ‖(F : G → ℂ) x‖ := le_rfl

/-- The conjugate-modulation `F ↦ class of (conj F ⬝ η)` on `Lp ℂ 2 μ`. -/
private def modConj (η : PontryaginDual G) (F : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (memLp_conj_mul_char μ F η).toLp _

private theorem coeFn_modConj (η : PontryaginDual G) (F : Lp ℂ 2 μ) :
    ⇑(modConj μ η F) =ᵐ[μ] fun x => conj ((F : G → ℂ) x) * ((η x : Circle) : ℂ) :=
  MemLp.coeFn_toLp _

private theorem norm_modConj_sub (η : PontryaginDual G) (F K : Lp ℂ 2 μ) :
    ‖modConj μ η F - modConj μ η K‖ = ‖F - K‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  have h1 : ⇑(modConj μ η F - modConj μ η K)
      =ᵐ[μ] fun x => conj ((F : G → ℂ) x - (K : G → ℂ) x) * ((η x : Circle) : ℂ) := by
    filter_upwards [Lp.coeFn_sub (modConj μ η F) (modConj μ η K),
      coeFn_modConj μ η F, coeFn_modConj μ η K] with x hx1 hx2 hx3
    rw [hx1, Pi.sub_apply, hx2, hx3, map_sub]
    ring
  rw [eLpNorm_congr_ae h1]
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [Lp.coeFn_sub F K] with x hx
  rw [norm_mul, RCLike.norm_conj, Circle.norm_coe, mul_one, hx, Pi.sub_apply]

private theorem continuous_modConj (η : PontryaginDual G) :
    Continuous (modConj μ η) := by
  refine Isometry.continuous (Isometry.of_dist_eq fun F K => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_modConj_sub μ η F K

private theorem modConj_toLp2Cc (η : PontryaginDual G) (v : G → ℂ) (hvc : Continuous v)
    (hvs : HasCompactSupport v)
    (hc : Continuous fun x => conj (v x) * ((η x : Circle) : ℂ))
    (hs : HasCompactSupport fun x => conj (v x) * ((η x : Circle) : ℂ)) :
    modConj μ η (toLp2Cc μ v hvc hvs)
      = toLp2Cc μ (fun x => conj (v x) * ((η x : Circle) : ℂ)) hc hs := by
  refine Lp.ext ?_
  refine (coeFn_modConj μ η _).trans ?_
  refine EventuallyEq.trans ?_ (coeFn_toLp2Cc μ _ hc hs).symm
  filter_upwards [coeFn_toLp2Cc μ v hvc hvs] with x hx
  rw [hx]

/-- The conjugate-composition `W ↦ class of (χ ↦ conj (W (χ⁻¹ ⬝ η)))` on the dual `L²`. -/
private theorem memLp_conj_comp (η : PontryaginDual G) (W : Lp ℂ 2 (dualHaar μ)) :
    MemLp (fun χ => conj ((W : PontryaginDual G → ℂ) (χ⁻¹ * η))) 2 (dualHaar μ) := by
  have h := ((Lp.memLp W).comp_measurePreserving
    (measurePreserving_inv_mul (dualHaar μ) η)).star
  refine h.ae_eq (Eventually.of_forall fun χ => ?_)
  rw [Pi.star_apply, RCLike.star_def]
  rfl

private def conjCompLp (η : PontryaginDual G) (W : Lp ℂ 2 (dualHaar μ)) :
    Lp ℂ 2 (dualHaar μ) :=
  (memLp_conj_comp μ η W).toLp _

private theorem coeFn_conjCompLp (η : PontryaginDual G) (W : Lp ℂ 2 (dualHaar μ)) :
    ⇑(conjCompLp μ η W)
      =ᵐ[dualHaar μ] fun χ => conj ((W : PontryaginDual G → ℂ) (χ⁻¹ * η)) :=
  MemLp.coeFn_toLp _

private theorem coeFn_conjCompLp_of_ae (η : PontryaginDual G)
    {W : Lp ℂ 2 (dualHaar μ)} {u : PontryaginDual G → ℂ} (hu : ⇑W =ᵐ[dualHaar μ] u) :
    ⇑(conjCompLp μ η W) =ᵐ[dualHaar μ] fun χ => conj (u (χ⁻¹ * η)) := by
  refine (coeFn_conjCompLp μ η W).trans ?_
  have h2 : (⇑W ∘ fun χ : PontryaginDual G => χ⁻¹ * η)
      =ᵐ[dualHaar μ] (u ∘ fun χ : PontryaginDual G => χ⁻¹ * η) :=
    (measurePreserving_inv_mul (dualHaar μ) η).quasiMeasurePreserving.ae_eq_comp hu
  filter_upwards [h2] with χ hχ
  show conj ((W : PontryaginDual G → ℂ) (χ⁻¹ * η)) = conj (u (χ⁻¹ * η))
  exact congrArg conj hχ

private theorem norm_conjCompLp_sub (η : PontryaginDual G)
    (W W' : Lp ℂ 2 (dualHaar μ)) :
    ‖conjCompLp μ η W - conjCompLp μ η W'‖ = ‖W - W'‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  have h1 : ⇑(conjCompLp μ η W - conjCompLp μ η W')
      =ᵐ[dualHaar μ] fun χ => conj ((W : PontryaginDual G → ℂ) (χ⁻¹ * η))
        - conj ((W' : PontryaginDual G → ℂ) (χ⁻¹ * η)) := by
    filter_upwards [Lp.coeFn_sub (conjCompLp μ η W) (conjCompLp μ η W'),
      coeFn_conjCompLp μ η W, coeFn_conjCompLp μ η W'] with χ hχ1 hχ2 hχ3
    rw [hχ1, Pi.sub_apply, hχ2, hχ3]
  rw [eLpNorm_congr_ae h1]
  have hdiff : AEStronglyMeasurable
      (fun ψ => conj ((W : PontryaginDual G → ℂ) ψ)
        - conj ((W' : PontryaginDual G → ℂ) ψ)) (dualHaar μ) :=
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable W)).sub
      (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable W'))
  calc eLpNorm (fun χ => conj ((W : PontryaginDual G → ℂ) (χ⁻¹ * η))
        - conj ((W' : PontryaginDual G → ℂ) (χ⁻¹ * η))) 2 (dualHaar μ)
      = eLpNorm ((fun ψ => conj ((W : PontryaginDual G → ℂ) ψ)
          - conj ((W' : PontryaginDual G → ℂ) ψ))
            ∘ fun χ : PontryaginDual G => χ⁻¹ * η) 2 (dualHaar μ) := rfl
    _ = eLpNorm (fun ψ => conj ((W : PontryaginDual G → ℂ) ψ)
          - conj ((W' : PontryaginDual G → ℂ) ψ)) 2 (dualHaar μ) :=
        eLpNorm_comp_measurePreserving hdiff
          (measurePreserving_inv_mul (dualHaar μ) η)
    _ = eLpNorm (⇑(W - W')) 2 (dualHaar μ) := by
        refine eLpNorm_congr_norm_ae ?_
        filter_upwards [Lp.coeFn_sub W W'] with ψ hψ
        rw [show conj ((W : PontryaginDual G → ℂ) ψ)
            - conj ((W' : PontryaginDual G → ℂ) ψ)
            = conj ((W : PontryaginDual G → ℂ) ψ - (W' : PontryaginDual G → ℂ) ψ) by
          rw [map_sub], RCLike.norm_conj, hψ, Pi.sub_apply]

private theorem continuous_conjCompLp (η : PontryaginDual G) :
    Continuous (conjCompLp μ η) := by
  refine Isometry.continuous (Isometry.of_dist_eq fun W W' => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_conjCompLp_sub μ η W W'

/-- **Intertwining**: the Plancherel isometry carries conjugate-modulation by `η` on `G` to
conjugate-composition with `χ ↦ χ⁻¹η` on the dual. -/
private theorem plancherelLI_modConj (η : PontryaginDual G) (F : Lp ℂ 2 μ) :
    plancherelLI μ (modConj μ η F) = conjCompLp μ η (plancherelLI μ F) := by
  refine funext_of_denseL2 μ (fun F => plancherelLI μ (modConj μ η F))
    (fun F => conjCompLp μ η (plancherelLI μ F))
    ((plancherelLI μ).continuous.comp (continuous_modConj μ η))
    ((continuous_conjCompLp μ η).comp (plancherelLI μ).continuous) ?_ F
  intro v hvc hvs
  have hc : Continuous fun x => conj (v x) * ((η x : Circle) : ℂ) :=
    (Complex.continuous_conj.comp hvc).mul
      (continuous_induced_dom.comp (map_continuous η))
  have hs : HasCompactSupport fun x => conj (v x) * ((η x : Circle) : ℂ) := by
    refine hvs.mono fun x hx => ?_
    simp only [mem_support] at hx ⊢
    intro h0
    refine hx ?_
    rw [h0, map_zero, zero_mul]
  show plancherelLI μ (modConj μ η (toLp2Cc μ v hvc hvs))
    = conjCompLp μ η (plancherelLI μ (toLp2Cc μ v hvc hvs))
  rw [modConj_toLp2Cc μ η v hvc hvs hc hs, plancherelLI_toLp2Cc μ _ hc hs,
    plancherelLI_toLp2Cc μ v hvc hvs]
  refine Lp.ext ?_
  have h1 : ⇑((memLp_two_fourierTransform_cc μ hc hs).toLp
      (fourierTransform μ fun x => conj (v x) * ((η x : Circle) : ℂ)))
      =ᵐ[dualHaar μ] fun χ => conj (fourierTransform μ v (χ⁻¹ * η)) := by
    refine (MemLp.coeFn_toLp _).trans ?_
    refine Eventually.of_forall fun χ => ?_
    exact fourierTransform_conj_mul_char μ v η χ
  have h2 : ⇑(conjCompLp μ η ((memLp_two_fourierTransform_cc μ hvc hvs).toLp
      (fourierTransform μ v)))
      =ᵐ[dualHaar μ] fun χ => conj (fourierTransform μ v (χ⁻¹ * η)) :=
    coeFn_conjCompLp_of_ae μ η (MemLp.coeFn_toLp _)
  exact h1.trans h2.symm

set_option maxHeartbeats 800000 in
-- A long proof: the polarized Plancherel identity and the geometry of the neighborhood
-- `B` are combined in a single construction.
/-- **Localized Fourier transforms.**  For every nonempty open set `Ω` in the dual group
there is an integrable function `Φ` on `G` whose Fourier transform does not vanish
identically but vanishes outside `Ω`.

`Φ` is the pointwise product of the Plancherel preimages of the indicators of a compact
symmetric neighborhood `B` of `1` and of its translate `B ⬝ χ₀` (`χ₀ ∈ Ω`, `B ⬝ B ⬝ χ₀ ⊆ Ω`);
its transform is *exactly* the convolution of the two indicators over `dualHaar μ`, by
polarization of the Plancherel identity. -/
theorem exists_integrable_fourierTransform_eq_zero_compl {Ω : Set (PontryaginDual G)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ∃ Φ : G → ℂ, Integrable Φ μ ∧ (∃ χ₀, fourierTransform μ Φ χ₀ ≠ 0) ∧
      ∀ χ ∉ Ω, fourierTransform μ Φ χ = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := hne
  -- a compact symmetric neighborhood `B` of `1` with `B * B * χ₀ ⊆ Ω`
  have hWopen : IsOpen ((fun ψ : PontryaginDual G => ψ * χ₀) ⁻¹' Ω) :=
    hΩ.preimage (continuous_mul_const χ₀)
  have hW1 : (1 : PontryaginDual G) ∈ (fun ψ : PontryaginDual G => ψ * χ₀) ⁻¹' Ω := by
    show (1 : PontryaginDual G) * χ₀ ∈ Ω
    rwa [one_mul]
  obtain ⟨V, hVopen, hV1, hVsub⟩ :=
    exists_open_nhds_one_mul_subset (hWopen.mem_nhds hW1)
  obtain ⟨C, hCcomp, hC1, hCV⟩ := exists_compact_subset hVopen hV1
  set B : Set (PontryaginDual G) := C ∩ C⁻¹ with hBdef
  have hBcomp : IsCompact B := hCcomp.inter_right hCcomp.inv.isClosed
  have hBnhds : B ∈ nhds (1 : PontryaginDual G) :=
    Filter.inter_mem (mem_interior_iff_mem_nhds.mp hC1)
      (inv_mem_nhds_one _ (mem_interior_iff_mem_nhds.mp hC1))
  have hBsymm : B⁻¹ = B := by
    rw [hBdef, Set.inter_inv, inv_inv, Set.inter_comm]
  have hBV : B ⊆ V := Set.inter_subset_left.trans hCV
  have hBmeas : MeasurableSet B := hBcomp.isClosed.measurableSet
  have hBfin : (dualHaar μ) B ≠ ∞ := hBcomp.measure_lt_top.ne
  have hBpos : (0 : ℝ≥0∞) < (dualHaar μ) B := by
    have h1 : (1 : PontryaginDual G) ∈ interior B := mem_interior_iff_mem_nhds.mpr hBnhds
    calc (0 : ℝ≥0∞) < (dualHaar μ) (interior B) :=
          isOpen_interior.measure_pos (dualHaar μ) ⟨1, h1⟩
      _ ≤ (dualHaar μ) B := measure_mono interior_subset
  set Kset : Set (PontryaginDual G) := (fun ψ => ψ * χ₀) '' B with hKdef
  have hKcomp : IsCompact Kset := hBcomp.image (continuous_mul_const χ₀)
  have hKmeas : MeasurableSet Kset := hKcomp.isClosed.measurableSet
  have hKfin : (dualHaar μ) Kset ≠ ∞ := hKcomp.measure_lt_top.ne
  -- the two indicator classes and their Plancherel preimages
  set OneB : PontryaginDual G → ℂ := B.indicator fun _ => (1 : ℂ) with hOneBdef
  set OneK : PontryaginDual G → ℂ := Kset.indicator fun _ => (1 : ℂ) with hOneKdef
  have hOneB2 : MemLp OneB 2 (dualHaar μ) :=
    memLp_indicator_const 2 hBmeas (1 : ℂ) (Or.inr hBfin)
  have hOneK2 : MemLp OneK 2 (dualHaar μ) :=
    memLp_indicator_const 2 hKmeas (1 : ℂ) (Or.inr hKfin)
  obtain ⟨a, ha⟩ := surjective_plancherelLI μ (hOneB2.toLp OneB)
  obtain ⟨b, hb⟩ := surjective_plancherelLI μ (hOneK2.toLp OneK)
  have hΦint : Integrable (fun x => (a : G → ℂ) x * (b : G → ℂ) x) μ :=
    (Lp.memLp a).integrable_mul (Lp.memLp b)
  -- the key identity: `𝓕Φ = OneB ⋆ OneK` pointwise on the dual
  have hkeyq : ∀ η : PontryaginDual G,
      fourierTransform μ (fun x => (a : G → ℂ) x * (b : G → ℂ) x) η
        = mconv (dualHaar μ) OneB OneK η := by
    intro η
    have h1 : fourierTransform μ (fun x => (a : G → ℂ) x * (b : G → ℂ) x) η
        = inner ℂ (modConj μ η b) a := by
      rw [L2.inner_def, fourierTransform_apply]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_modConj μ η b] with x hx
      show (a : G → ℂ) x * (b : G → ℂ) x * conj ((η x : Circle) : ℂ)
        = inner ℂ ((modConj μ η b : G → ℂ) x) ((a : G → ℂ) x)
      rw [RCLike.inner_apply, hx, map_mul, RCLike.conj_conj]
      ring
    have h2 : inner ℂ (modConj μ η b) a
        = inner ℂ (plancherelLI μ (modConj μ η b)) (plancherelLI μ a) :=
      ((plancherelLI μ).inner_map_map (modConj μ η b) a).symm
    have h3 : plancherelLI μ (modConj μ η b) = conjCompLp μ η (hOneK2.toLp OneK) := by
      rw [plancherelLI_modConj μ η b, hb]
    have h4 : inner ℂ (conjCompLp μ η (hOneK2.toLp OneK)) (hOneB2.toLp OneB)
        = ∫ χ, OneB χ * OneK (χ⁻¹ * η) ∂(dualHaar μ) := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_conjCompLp_of_ae μ η hOneK2.coeFn_toLp,
        hOneB2.coeFn_toLp] with χ hχ1 hχ2
      show inner ℂ ((conjCompLp μ η (hOneK2.toLp OneK) : PontryaginDual G → ℂ) χ)
        ((hOneB2.toLp OneB : PontryaginDual G → ℂ) χ) = OneB χ * OneK (χ⁻¹ * η)
      rw [RCLike.inner_apply, hχ1, hχ2, RCLike.conj_conj]
    rw [h1, h2, h3, ha, h4]
    rfl
  -- nonvanishing at `χ₀`
  have hBrealpos : 0 < (dualHaar μ).real B := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hBpos.ne' hBfin
  have hval : fourierTransform μ (fun x => (a : G → ℂ) x * (b : G → ℂ) x) χ₀
      = (((dualHaar μ).real B : ℝ) : ℂ) := by
    rw [hkeyq χ₀]
    have hpt : ∀ χ : PontryaginDual G, OneB χ * OneK (χ⁻¹ * χ₀) = OneB χ := by
      intro χ
      by_cases hχ : χ ∈ B
      · have hinv : χ⁻¹ ∈ B := by
          rw [← hBsymm]
          exact Set.inv_mem_inv.mpr hχ
        have hK : χ⁻¹ * χ₀ ∈ Kset := ⟨χ⁻¹, hinv, rfl⟩
        rw [hOneBdef, hOneKdef]
        rw [Set.indicator_of_mem hχ, Set.indicator_of_mem hK, mul_one]
      · rw [hOneBdef]
        rw [Set.indicator_of_notMem hχ, zero_mul]
    calc mconv (dualHaar μ) OneB OneK χ₀
        = ∫ χ, OneB χ ∂(dualHaar μ) := by
          rw [mconv_apply]
          exact integral_congr_ae (Eventually.of_forall hpt)
      _ = ((dualHaar μ).real B) • (1 : ℂ) := integral_indicator_const (1 : ℂ) hBmeas
      _ = (((dualHaar μ).real B : ℝ) : ℂ) := by rw [Complex.real_smul, mul_one]
  refine ⟨fun x => (a : G → ℂ) x * (b : G → ℂ) x, hΦint, ⟨χ₀, ?_⟩, ?_⟩
  · rw [hval]
    exact Complex.ofReal_ne_zero.mpr hBrealpos.ne'
  · -- vanishing outside `Ω`
    intro η hη
    rw [hkeyq η, mconv_apply]
    have hpt : ∀ χ : PontryaginDual G, OneB χ * OneK (χ⁻¹ * η) = 0 := by
      intro χ
      by_cases h1 : χ ∈ B
      · by_cases h2 : χ⁻¹ * η ∈ Kset
        · exfalso
          obtain ⟨β, hβ, hβeq⟩ := h2
          have hηeq : χ * β * χ₀ = η := by
            have hβeq' : β * χ₀ = χ⁻¹ * η := hβeq
            rw [mul_assoc, hβeq', mul_inv_cancel_left]
          have hmem : χ * β ∈ V * V := Set.mul_mem_mul (hBV h1) (hBV hβ)
          have hW : (χ * β) * χ₀ ∈ Ω := hVsub hmem
          rw [hηeq] at hW
          exact hη hW
        · rw [hOneKdef]
          rw [Set.indicator_of_notMem h2, mul_zero]
      · rw [hOneBdef]
        rw [Set.indicator_of_notMem h1, zero_mul]
    calc ∫ χ, OneB χ * OneK (χ⁻¹ * η) ∂(dualHaar μ)
        = ∫ _χ, (0 : ℂ) ∂(dualHaar μ) :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = 0 := integral_zero _ _

end Localized

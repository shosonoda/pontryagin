# Upstreaming report: what should go into Mathlib, and how

**Scope.** Every item in this repository, audited at commit `dab1430` against the pinned
Mathlib (v4.32.0 toolchain, checkout under `.lake/packages/mathlib`). Every "Mathlib
already has X" claim below was verified by grep against that checkout and cites the
exact declaration found; every "absent from Mathlib" claim was also grep-verified.

**Method.** Five parallel audits covered the 21 proof modules; each public declaration
received a verdict, a target Mathlib location, the changes required, and a priority.
This document consolidates those audits, the cross-cutting cleanups, and a single
dependency-ordered PR roadmap.

**Verdict legend.**
- **upstream as-is** — mathematically and structurally ready; only mechanical polish.
- **upstream after changes** — belongs in Mathlib after the stated redesign
  (naming, bundling, typeclass minimization, generalization).
- **possibly redundant** — Mathlib has the fact or an easy derivation; citation given.
- **skip** — project-specific scaffolding (comparator artifacts, choice-plumbing,
  trivial compositions); not upstream material.

---

## Executive summary

This repository contains the first formalization of harmonic analysis on general
locally compact abelian groups: essentially **none of the main theory exists in
Mathlib** (verified: no positive-definite functions, no Bochner theorem, no dual/
Plancherel measure, no LCA Fourier transform or Riemann–Lebesgue beyond
inner-product spaces, no L¹ convolution algebra on any `Lp`, no Stone–Weierstrass for
C₀ — the latter is an explicit "Future work" note in Mathlib's own
`StoneWeierstrass.lean:45-48` — and no Pontryagin duality theorem, though
`Mathlib/Topology/Algebra/PontryaginDual.lean`'s docstring advertises it as the
motivating example).

Headline upstream targets, in rough order of mathematical weight:

1. **Pontryagin duality itself** — `eval`, `eval_injective`, `isInducing_eval`,
   `isClosed_range_eval`, `eval_surjective`, `toDoubleDual` (proposed Mathlib name
   `PontryaginDual.doubleDualEquiv`), all with measure-free statements.
2. **Bochner's theorem** (`IsPositiveType.exists_bochner_measure` + uniqueness + mass).
3. **The dual Haar measure** (`dualHaar` + Haar instances + the density identity) and
   **Fourier inversion** (`IsPositiveType.fourier_inversion`).
4. **Plancherel theory** (Parseval, the surjective isometry `plancherelLI`, localized
   transforms, dual L¹-uniqueness).
5. **The LCA Fourier transform** with the general **Riemann–Lebesgue lemma**
   (strictly more general than Mathlib's inner-product-space version, and its
   continuity proof needs no first-countability, unlike
   `VectorFourier.fourierIntegral_continuous`).
6. **The L¹(G) convolution Banach *-algebra** with its approximate identity, plus the
   **spectrum theorem** (characters of L¹(G) ↔ Ĝ) — no `Lp` in Mathlib carries any
   multiplication today.
7. **Positive-definite functions** (`IsPositiveType`) — a missing basic definition.
8. **Stone–Weierstrass for C₀** — directly requested by Mathlib's own TODO.
9. A collection of **independently valuable leaf lemmas** (locally compact subspaces
   are locally closed; locally compact subgroups are closed; C_c density in Lp on
   locally compact Hausdorff spaces; C_c testing lemmas; one-variable-compact-support
   Fubini for finite inner-regular measures; normalized bumps; simultaneous L¹∩L²
   approximation; the ball-clamp projection inequality; C₀ ↔ one-point-compactification
   API; equicontinuity of compact character sets; a complex Riesz representation for
   positive functionals on C₀ hidden inside `Bochner.lean` that should be factored out).

Roughly **80 % of the public surface should reach Mathlib** in some form; the
remainder is comparator scaffolding, choice-based extension plumbing that disappears
under better bundling, or one-line consequences of existing Mathlib lemmas
(all listed in "Do not upstream" below).

The two biggest systematic review battles to expect:
- **Packaging of C_c functions**: the project's unbundled `toLpCc`-style constructors
  must be replaced by a bundled `CompactlySupportedContinuousMap.toLp`
  (`C_c(α, E) →L[𝕜] Lp E p μ`) — the missing sibling of
  `BoundedContinuousFunction.toLp` and `ContinuousMap.toLp`.
- **Per-lemma typeclass minimization**: the project deliberately uses one coarse
  hypothesis block per file plus `set_option linter.unusedSectionVars false`; Mathlib
  will require minimal hypotheses per lemma (many need only `IsMulLeftInvariant` or
  `IsInvInvariant`, not `IsHaarMeasure + Regular`) and will not accept file-scoped
  linter opt-outs or the `maxHeartbeats` bumps without proof-splitting.

---

## Module-by-module findings

### Pontryagin/Topology.lean (116 lines)

Two general facts, both genuine gap-fillers: Mathlib has only the *converse*
(`IsLocallyClosed.locallyCompactSpace`, `Mathlib/Topology/Compactness/LocallyCompact.lean:216`),
and for subgroups only `Subgroup.isClosed_of_discrete`
(`Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean:273` — strictly weaker, since
discrete ⇒ locally compact) and `Subgroup.isClosed_of_isOpen`
(`Mathlib/Topology/Algebra/OpenSubgroup.lean:273`).

| declaration | verdict | target | notes |
|---|---|---|---|
| `IsLocallyClosed.of_locallyCompactSpace` | upstream as-is | `Mathlib/Topology/Compactness/LocallyCompact.lean` | Name matches the `X.of_locallyCompactSpace` precedent. Add companion `IsEmbedding.isLocallyClosed_range` (absent). High value. |
| `Subgroup.isClosed_of_locallyCompactSpace` | upstream after changes | `Mathlib/Topology/Algebra/Group/Compact.lean` | Add `@[to_additive]`. Factor the second half as standalone `Subgroup.isClosed_of_isLocallyClosed` via `IsLocallyClosed.isOpen_preimage_val_closure` (`LocallyClosed.lean:194`) + `isClosed_of_isOpen` — replaces ~55 lines of translate-cover argument with ~10. High value. |

### Pontryagin/CcFubini.lean (235 lines)

The headline swap is a **pure re-export**: Mathlib's
`MeasureTheory.integral_integral_swap_of_hasCompactSupport`
(`Mathlib/MeasureTheory/Integral/Prod.lean:602`) is already stated in curried form.
The slice/partial-integral API, however, is new — and
`Mathlib/MeasureTheory/Measure/Haar/Unique.lean:94,154` re-derives these facts
inline, evidence they are worth having.

| declaration | verdict | target | notes |
|---|---|---|---|
| `integral_integral_swap_of_continuous_compactSupport` | skip (redundant) | — | Byte-for-byte restatement of `Prod.lean:602`. |
| `HasCompactSupport.uncurry_left` / `_right` | upstream as-is | `Mathlib/Topology/Algebra/Support.lean` | Names match `Continuous.uncurry_left/right` (`Constructions/SumProd.lean:227`). |
| `HasCompactSupport.exists_support_subset_prod` | upstream as-is | same | Strengthen conclusion to `tsupport … ⊆ K₁ ×ˢ K₂`. |
| `Continuous.integrable_uncurry_left` / `_right` | upstream as-is | `Mathlib/MeasureTheory/Function/LocallyIntegrable.lean` | Next to `Continuous.integrable_of_hasCompactSupport` (line 622). |
| `continuous_integral_right` / `_left` | possibly redundant | — | Subsumed by the stronger FiniteMeasureFubini variants; upstream only those. |
| `hasCompactSupport_integral_right` / `_left`, `integrable_integral_right` / `_left` | upstream as-is | `LocallyIntegrable.lean` / `Bochner/Set.lean` | The reusable API that Haar-uniqueness proofs currently re-derive ad hoc. |
| `norm_integral_integral_le_of_support_subset` | upstream after changes | `Integral/Prod.lean` | Weaken the bound hypothesis to the support. Low-medium value. |

### Pontryagin/FiniteMeasureFubini.lean (225 lines)

Genuinely new: Mathlib has exactly two `integral_integral_swap*` lemmas (product-
integrable + SFinite at `Prod.lean:481`; joint compact support at `Prod.lean:602`);
nothing covers a finite inner-regular measure against a kernel compactly supported in
one variable. This is precisely the missing Fubini infrastructure for non-σ-compact
spaces.

| declaration | verdict | target | notes |
|---|---|---|---|
| `continuous_integral_right_of_forall_compl_eq_zero` / `_left_…` | upstream after changes | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` | Rename `continuous_integral_of_compact_support`; keep one variant (other = `Prod.swap`). Fills a gap: the existing `continuous_parametric_integral_of_continuous` (line 1129) demands first-countability + second-countability that this avoids. |
| `integral_integral_swap_of_finite_of_compactSupport` | upstream after changes | `Mathlib/MeasureTheory/Integral/Regular.lean` (or a new small file) | Rename e.g. `integral_integral_swap_of_isFiniteMeasure_of_compactSupport`; state with `[RegularSpace X]` instead of T2 (free generalization — Urysohn needs only regular + LC); docstring should advertise the no-product-σ-algebra selling point. A reviewer may ask to factor the compact-exhaustion + cutoff-sequence steps into a reusable `InnerRegularCompactLTTop` lemma. High value for LCA work. |

### Pontryagin/Density.lean (284 lines) and Pontryagin/DensityLp.lean (173 lines)

Two halves. (a) **C_c density in Lp without `NormalSpace`**: Mathlib's
`ContinuousMapDense.lean` carries `variable [NormalSpace α]` (line 66), and Mathlib
has *no* route to `NormalSpace` for general locally compact Hausdorff spaces or LC
groups (checked: compact+R1, Lindelöf, second-countable, σ-compact-paracompact only).
The right upstream move is to **fix Mathlib's file in place** — replace the
`NormalSpace + WeaklyLocallyCompactSpace` hypotheses of the compactly-supported block
(`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, line 135, and its three
`Integrable.*` corollaries) by `RegularSpace + LocallyCompactSpace`, using the
LC Urysohn lemma. Honest caveat for the PR: this is not a pointwise weakening
(neither hypothesis set implies the other), but every actual consumer is locally
compact regular, and LCH spaces — the natural habitat of `HasCompactSupport` — are
covered only by the new version. One audit reported the pinned file's hypotheses
differently; re-verify the exact section structure of `ContinuousMapDense.lean` when
preparing the PR (empirically, the project *had* to reprove the lemma at build time).
(b) **L¹ separation by C_c testing**: genuinely new on LCH spaces; closest Mathlib
results are the smooth-test-function lemmas in
`Analysis/Distribution/AEEqOfIntegralContDiff.lean` (σ-compact manifolds only).

| declaration | verdict | target | notes |
|---|---|---|---|
| `exists_continuous_eLpNorm_indicator_sub_le` (Density) | skip (subsumed) | — | `p = 1` case of the primed DensityLp version. |
| `exists_hasCompactSupport_integral_norm_sub_le` (Density) | possibly redundant after the fix | `ContinuousMapDense.lean` | Statement-identical to Mathlib's `Integrable.exists_hasCompactSupport_integral_sub_le` (line 222) modulo hypotheses; do not upstream as a new name. |
| `norm_L1_le_of_forall_integral_le` | upstream after changes | new `Mathlib/MeasureTheory/Integral/AEEqOfIntegralCc.lean` | Quantitative L¹ bound from testing against `‖φ‖ ≤ 1` C_c functions, no L¹–L∞ duality. **Delete the unused `hC` hypothesis and the linter opt-out**; rename (capital `L1` violates conventions), e.g. `Integrable.integral_norm_le_of_forall_integral_mul_le`; generalize ℂ → `RCLike`. Medium-high value. |
| `ae_eq_zero_of_forall_integral_mul_eq_zero` | upstream after changes | same new file | The continuous-C_c analogue of `ae_eq_zero_of_integral_contDiff_smul_eq_zero`; reshape to the `smul` idiom with real-valued tests; a `LocallyIntegrable` version is the natural follow-up. High value. |
| `exists_continuous_eLpNorm_indicator_sub_le'` (DensityLp) | upstream after changes | `ContinuousMapDense.lean` | Becomes the internal approximation step; generalize ℂ → `E` (proof is already smul-shaped); drop the prime. |
| `MemLp.exists_hasCompactSupport_eLpNorm_sub_le'` | upstream after changes (replaces Mathlib lemma) | `ContinuousMapDense.lean:135` | Modify the existing lemma in place, not a primed sibling; corollaries inherit the fix. High value — unblocks `ContinuousMapDense` for LCH groups. |
| `dense_ccLp` | upstream after changes | same | Reshape as `CompactlySupportedContinuousMap.toLp` + `toLp_denseRange`, mirroring `BoundedContinuousFunction.toLp_denseRange` (line 349). The set-of-classes formulation will not pass review. |
| `dense_ccL2` | skip | — | Trivial `p = 2` instantiation. |

### Pontryagin/StoneWeierstrassC0.lean (217 lines)

Fills an explicitly acknowledged Mathlib gap:
`Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean:45-48` — *"Future work — Extend
to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact spaces."* The only non-unital SW result in Mathlib is the
singly-generated compact-subset case `ContinuousMapZero.adjoin_id_dense` (line 628).
Also verified: nothing in Mathlib connects `ZeroAtInfty` with `OnePoint`, so the
embedding API is new and independently valuable (e.g. for C*-unitization work).

| declaration | verdict | target | notes |
|---|---|---|---|
| `ZeroAtInftyContinuousMap.toContinuousMapOnePoint` (+ simp lemmas) | upstream as-is | `Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean` | `[R1Space X]` is the right minimal hypothesis. High value standalone API. |
| `isometry_toContinuousMapOnePoint` | upstream as-is | same | Also expose `IsEmbedding`/`IsClosedEmbedding` (range = ker of eval at ∞) corollaries. |
| `toContinuousMapOnePointHom` | upstream as-is | same | Optionally bundle further as a `NonUnitalStarAlgHom` isometry. |
| `nonUnitalStarSubalgebra_dense_of_separatesPoints` | upstream after changes | new `Mathlib/Topology/ContinuousMap/StoneWeierstrassZeroAtInfty.lean` | A sibling file avoids import bloat (`StoneWeierstrass.lean` has `assert_not_exists Unitization`). Reshape `hsep` via `Set.SeparatesPoints`; delete Mathlib's "Future work" note in the PR. High value — pre-requested by Mathlib's own TODO. |
| `nonUnitalStarSubalgebra_topologicalClosure_eq_top_of_separatesPoints` | upstream as-is | same | Mirrors the compact-case naming exactly. |

### Pontryagin/Translation.lean (223 lines)

Largely scaffolding over API Mathlib already has: the `translateLp` half is covered by
`Lp.compMeasurePreservingₗᵢ` (`LpSpace/Basic.lean:630`) and the `DomMulAct` action
(`LpSpace/DomAct/Basic.lean`, `DomAct/Continuous.lean:53` — whose joint continuity is
*strictly stronger* than the project's `continuous_translateLp`, under weaker
typeclasses). The genuinely new items are the multiplicativization of `translate` and
the normalized-bump lemma.

| declaration | verdict | target | notes |
|---|---|---|---|
| `mtranslate` + `_apply`/`_one`/`_mtranslate` | upstream after changes | `Mathlib/Algebra/Group/Translate.lean` | Mathlib's additive `translate` (`τ`) has **no multiplicative version and no `to_additive` link**; restate `translate` as the `to_additive` shadow of a new multiplicative def. Resolve the left-translation (`f (a⁻¹x)`) vs `f (x - a)` convention; only `Group` needed. |
| `support_mtranslate`, `HasCompactSupport.mtranslate`, `Continuous.mtranslate` | possibly redundant / trivial | — | Additive `support_translate` exists (`Translate.lean:88`); come free with `to_additive`. |
| `tsupport_mtranslate` | upstream after changes | Translate follow-up | No Mathlib analog. |
| `exists_normalized_bump` | **upstream after changes — high value** | near `MeasureTheory/Integral/PeakFunction.lean` or `Haar/Unique.lean` | Nothing comparable exists (`exists_continuous_nonneg_pos` has no support control/normalization; `ContDiffBump` is ℝⁿ-only). Generalize: no group structure needed — any point of a locally compact R1 space, `[μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]`. Consider returning a bundled `C_c(X, ℝ)`. Key ingredient for approximate-identity work. |
| `eLpNorm_mtranslate`, `MemLp.mtranslate`, `integral_mtranslate` | upstream after changes (low) | `MeasureTheory/Group/Integral.lean` | Wrappers; need only `[IsMulLeftInvariant μ]`. |
| `translateLp` + its 5 lemmas + `continuous_translateLp` | possibly redundant | — | Use `DomMulAct`/`compMeasurePreservingₗᵢ` upstream instead (see citations above); drop from the plan. |

### Pontryagin/Convolution.lean (427 lines)

The strongest upstream candidate of its group. Mathlib's additive
`Analysis/Convolution.lean` header TODO explicitly asks for `@[to_additive]` and for
ℒᵖ×ℒᵠ continuity (lines 74–84); the new `MeasureTheory.mlconvolution`
(`Analysis/LConvolution.lean:50`) sets the naming/`to_additive` precedent for a
multiplicative Bochner convolution. **Naming caveat**: `mconv` is taken by
`MeasureTheory.Measure.mconv` (measure convolution `∗ₘ`,
`MeasureTheory/Group/Convolution.lean:35`); the function version should be
`MeasureTheory.mconvolution`, taking Mathlib's bilinear `L` rather than hardcoding ℂ.
A selling point to state in every PR: the C_c proofs remove the `SFinite` and
`MeasurableMul₂`/`MeasurableAdd₂` hypotheses that Mathlib's additive lemmas require
and that **fail on general (non-σ-compact, non-second-countable) LCA groups**.

| declaration | verdict | target | notes |
|---|---|---|---|
| `mstar` + apply/involution/continuity/support lemmas | upstream after changes | with `mconvolution` | No Mathlib counterpart; generalize ℂ → `RCLike`/star normed ring; name discussion needed (harmonic-analysis `f^*`). |
| `mconv` + `mconv_apply` | **upstream after changes — high value** | new file next to `Analysis/Convolution.lean` | Rename; bilinear-`L` form; attempt `@[to_additive]` link to `convolution` (LConvolution proves the pattern works). Closes an explicit Mathlib TODO. |
| `integral_mstar` | upstream after changes | with `mstar` | Needs only `[IsInvInvariant μ]` — minimize. |
| `measurePreserving_inv_mul` | possibly redundant | — | = `measurePreserving_div_left` (`Group/Measure.lean:387`) on `CommGroup`. |
| `eLpNorm_comp_inv`, `MemLp.comp_inv` | upstream as-is | `MeasureTheory/Group/Integral.lean` | Natural `@[to_additive]` companions to `integral_inv_eq_self`. |
| `eLpNorm_mstar`, `MemLp.mstar`, `eLpNorm_shift`, `MemLp.shift` | upstream after changes | group Lp file | Rename `shift`; generalize scalar. `memLp_two_shift`/`eLpNorm_two_shift`: skip (p=2 specializations). |
| `mconv_congr_ae` | upstream after changes | with `mconvolution` | *Improvement* over additive `convolution_congr` (`Convolution.lean:496`): no `MeasurableAdd₂ + SFinite` needed. |
| `Continuous.mconv`, `HasCompactSupport.mconv`, `tsupport_mconv_subset` | upstream after changes | with `mconvolution` | Mirror the generality of the additive `HasCompactSupport.continuous_convolution_right` (:601) etc. |
| `integral_mconv` | upstream after changes | with `mconvolution` | Additive version (:845) needs SFinite + MeasurableAdd₂; C_c version removes both. |
| `integral_norm_mconv_le` | **upstream after changes — high value** | with `mconvolution` | Young's L¹ inequality. Mathlib has **no norm inequality for convolutions at all** (grep verified). State the additive version too. |
| `mconv_comm`, `mconv_assoc` | upstream after changes | with `mconvolution` | Additive analogs exist with heavier hypotheses (`convolution_flip` :642, `convolution_assoc` :882); drop `mconv_assoc`'s unused hypothesis. |
| `mstar_mconv`, `mtranslate_mconv`, `mconv_mtranslate` | upstream after changes | with `mconvolution` | No additive analogs exist (no translate-of-convolution lemma in Mathlib). |
| `norm_mconv_le_of_memLp_two`, `continuous_mconv_of_memLp_two` | **upstream after changes — high value** | with `mconvolution` + additive counterpart | Directly answers Convolution.lean's Fremlin-255K TODO for p = q = 2. Route through `DomMulAct` upstream; generalize ℂ → `RCLike`. |
| `mconv_mstar_self_one` | upstream after changes (low) | with `mstar` | `(f ⋆ f^*)(1) = ‖f‖₂²`; pairs with the positive-definiteness PR. |
| kernel helpers (`mconv_kernel_*`) | skip | — | Keep private upstream. |

### Pontryagin/DualPolars.lean (291 lines)

Natural companions to Mathlib's `PontryaginDual.lean` and `Circle.lean`. One block
(`isCompact_polar`) near-verbatim duplicates the Arzelà–Ascoli core of Mathlib's own
`ContinuousMonoidHom.locallyCompactSpace_of_equicontinuousAt`
(`Topology/Algebra/Group/CompactOpen.lean:149-183`) — the right upstream move is a
de-duplicating refactor.

| declaration | verdict | target | notes |
|---|---|---|---|
| `Circle.closure_centeredArc`, `mem_closure_centeredArc` | upstream as-is | `Analysis/SpecialFunctions/Complex/Circle.lean` | Fits the existing `centeredArc` API; nothing there computes closures. |
| `Circle.abs_arg_le_div_of_pow_mem_centeredArc` | upstream after changes | same | Quantitative no-small-subgroups; generalize `π/4` to any `r ≤ π/2`. |
| `Circle.norm_coe_sub_one_le_abs_arg` | possibly redundant | optional one-liner | Two lines from `Complex.norm_exp_I_mul_ofReal_sub_one_le` (`Trigonometric/Bounds.lean:260`) + `Circle.exp_arg`; don't upstream the `nlinarith` proof. |
| `ContinuousEvalConst` instance for the dual | upstream as-is | `PontryaginDual.lean` | Genuinely missing from the `deriving` list (line 66). |
| `PontryaginDual.polar` + `mem_polar`/`one_mem_polar`/`polar_anti`/`isClosed_polar` | upstream after changes | `PontryaginDual.lean` | Reshape via `Set.MapsTo`; parametrize the arc; document naming vs `NormedSpace.polar`. |
| `isCompact_polar` | **upstream after changes — high value** | refactor of `Group/CompactOpen.lean` + corollary | Extract a general `ContinuousMonoidHom.isCompact_setOf_mapsTo` (equicontinuous into a closed compact target ⇒ compact), re-derive Mathlib's LCS instance from it; the polar result becomes a short corollary, and needs **no local compactness of G**. |
| `hasBasis_nhds_one`, `hasBasis_nhds` | upstream after changes | `PontryaginDual.lean` | No explicit nhds basis for the dual exists in Mathlib. `hasBasis_nhds_one` needs no `IsTopologicalGroup G`. |
| `eventually_mem_centeredArc`, `eventually_uniform_arc` | upstream as-is | `PontryaginDual.lean` | Direct corollaries of the basis. |

### Pontryagin/L1Algebra.lean (896 lines)

The L¹(G) convolution Banach *-algebra — a well-known missing piece: **no `Lp` in
Mathlib carries any multiplication** (grep verified). The mathematics should
upstream; nearly all packaging will be renegotiated.

| declaration | verdict | target | notes |
|---|---|---|---|
| `integrable_mconv_integrand`, `mconv_add_left/right`, `mconv_smul_left/right` | upstream after changes | with `mconvolution` | Additive analogs `ConvolutionExistsAt.distrib_add` (:455), `smul_convolution` (:439) — near-free with a bilinear-`L` definition. |
| `toLpCc` + `coeFn`/`congr`/`norm` lemmas | upstream after changes | `MeasureTheory/Function/LpSpace/ContinuousFunctions.lean` | Reshape as bundled `CompactlySupportedContinuousMap.toLp : C_c(α, E) →L[𝕜] Lp E p μ` (`[IsFiniteMeasureOnCompacts μ]`) — verified missing. The unbundled 3-argument constructor will not survive review. |
| `cc_rep_unique` | **redundant** | — | Exactly `Continuous.ae_eq_iff_eq` (`MeasureTheory/Measure/OpenPos.lean:141`). |
| `norm_sub_eq_integral` | possibly redundant | — | From `L1.norm_eq_integral_norm` (`Integral/Bochner/Basic.lean:904`) + `Lp.coeFn_sub`. |
| `ccSubmodule` + membership/density/`subtypeL` lemmas | upstream after changes | ContinuousFunctions + ContinuousMapDense | Becomes `LinearMap.range` + `DenseRange` of the bundled map; the density content is the ContinuousMapDense fix (see Density above). |
| `funext_of_dense` | skip | — | Thin wrapper of `Continuous.ext_on`; use inline. |
| `ccRep*` family | skip (implementation) | — | `Exists.choose` plumbing; disappears under the `C_c(G, ℂ)`-typed design. |
| `ccMul*` family + `ccMulCLM` | upstream after changes | L¹-algebra file | Content right; repackage source as `C_c(G, ℂ)` with `LinearMap.mkContinuous₂`. |
| `mulCLM` + agreement/norm lemmas | **upstream after changes — the headline** | new `Mathlib/Analysis/Fourier/L1ConvolutionAlgebra.lean` (name TBD) | Double `ContinuousLinearMap.extend`-flip-extend is sound and pure-Mathlib. The PR must argue *why density extension instead of the direct integral formula*: `Integrable.integrable_convolution` needs `SFinite + MeasurableMul₂`, which fail on general LCA groups. The agreement lemma `mulCLM_toLpCc` is the load-bearing API. `mulCLMAux` private. |
| `mulCLM_comm`, `mulCLM_assoc` | upstream after changes | same | Shorter with `DenseRange.induction_on₂/₃`. |
| `L1star` family (11 lemmas) | upstream after changes | same | Bundle as a conjugate-linear isometric involution; most lemmas become instance fields. |
| `L1G` synonym + `ofLp`/`toLp` + transport lemmas | upstream after changes | same | Design flags for reviewers: synonym vs instances directly on `Lp ℂ 1 μ` (synonym defensible — a global `Mul (Lp ℂ 1 μ)` keyed on `[μ.IsHaarMeasure]` is surprising); `L1G` is not a Mathlib-style name; `ofLp`/`toLp` should be one bundled `LinearIsometryEquiv`; ℂ → `RCLike` works verbatim; abelian-only scope should be stated (general G needs the modular function for star). |
| instances (`NonUnitalNormedCommRing`, `IsScalarTower`, `SMulCommClass`, `StarRing`, `StarModule`, `NormedStarGroup`, `CompleteSpace`) + `norm_star` | **upstream after changes — high value** | same | No competitor in Mathlib. Check the minimal import for `NormedStarGroup` (currently pulls `CStarAlgebra/Basic`). |
| `exists_bump_mconv_close`, `L1G.bump`, `norm_bump`, `exists_bump_mul_close` | upstream after changes | same (approximate-identity section) | The ε-form is deliberate — the nhds filter of a general group is not countably generated, so filter-DCT is unusable; say so in the docstring. Also offer a `Filter.Tendsto` phrasing along `(nhds 1).smallSets` for composability. |

### Pontryagin/FourierTransform.lean (530 lines)

The LCA Fourier transform. Mathlib has only the vector-space framework
(`VectorFourier.fourierIntegral`), `AddCircle`/`ZMod`/finite-abelian cases, and
Riemann–Lebesgue for inner-product spaces. Nothing here is redundant; everything
needs namespace/typeclass work.

**Convention reconciliation** (the key design task): Mathlib's convention is
`e (-L v w) • f v` with an additive character; ours is `f x * conj (χ x)` with
`χ : PontryaginDual G`. They agree: `conj (χ x) = ((χ x)⁻¹ : ℂ) = (χ⁻¹) x`, so the
upstream definition should be `PontryaginDual.fourierIntegral (μ) (f : G → E) (χ) :=
∫ x, (χ x)⁻¹ • f x ∂μ` for any ℂ-Banach `E` (`mul conj` as a rewrite lemma), with a
compatibility lemma to `VectorFourier.fourierIntegral` via `χ_w x = e (L x w)`.
Multiplicative-only is acceptable — `PontryaginDual` has no additive twin, so
`to_additive` cannot fire; precedent: `Measure.mconv`/`conv`.

| declaration | verdict | target | notes |
|---|---|---|---|
| `Circle.sqrt_two_div_two_le_norm_coe_sub_one` | upstream after changes | `Circle.lean` (or private in the RL file) | Derive from `Complex.norm_exp_I_mul_ofReal_sub_one` (`Analysis/Complex/Trigonometric.lean:973`). |
| `PontryaginDual.norm_coe_sub_coe` | upstream as-is | `PontryaginDual.lean` | Small but repeatedly used. |
| `fourierTransform` + `_apply` | upstream after changes | new `Mathlib/Analysis/Fourier/LCA/FourierTransform.lean` | Namespace + `fourierIntegral`-style name; Banach codomain via `(χ x)⁻¹ • f x`; definition needs no Haar. Top priority. |
| `_congr_ae`, `_smul`, `norm_…_le`, `_add`, `_sub`, `norm_…_sub_le` | upstream as-is (renames) | same | Keep names parallel to `VectorFourier.*`; minimize hypotheses per lemma. |
| `Integrable.mul_conj_char` | upstream after changes | same | Strengthen to an iff (`fourierIntegral_convergent_iff` analog). |
| `fourierTransform_mstar`, `_mtranslate`, `_mul_char`, `_mconv` | upstream after changes | same / LCA-convolution file | Need only inv-/left-invariance; `_mconv` closes the convolution theorem for C_c. |
| `continuous_fourierTransform` | upstream as-is | same | **Strictly more general** than `VectorFourier.fourierIntegral_continuous` (no first-countability); advertise. |
| `tendsto_fourierTransform_cocompact` | upstream as-is | new `…/LCA/RiemannLebesgueLemma.lean` | **Flagship**: the general-LCA Riemann–Lebesgue lemma. |
| `exists_nhds_forall_bump_fourierTransform_close` | upstream after changes | approximate-identity file | Make the private equicontinuity helper public (`PontryaginDual.exists_nhds_one_forall_norm_coe_sub_one_le`). |

### Pontryagin/Spectrum.lean (711 lines) and Pontryagin/UnitizationSpectrum.lean (204 lines)

The Gelfand theory of L¹(G). Nothing comparable in Mathlib (its Gelfand theory is
abstract; `Lp.fourierTransformCLM` reaches only `→ᵇ` on real vector spaces). Gated on
the L¹-algebra PR; expect design bikeshedding on the `L1G` packaging.

| declaration | verdict | target | notes |
|---|---|---|---|
| `fourierTransform_coeFn_toLpCc`, `norm_fourierTransform_coeFn_sub_le`, `continuous_fourierTransform_coeFn` | upstream after changes | `…/LCA/FourierHom.lean` | The 1-Lipschitz statement is the keeper; the rest re-derives from the final C_c→L¹ API. |
| `L1G.fourier` family, `fourierC0`, `fourierHom` | upstream after changes | same | The C₀-valued `NonUnitalStarAlgHom` bundling is the right object (stronger than Mathlib's `Lp.fourierTransformCLM`); add `norm_fourierHom_apply_le`. |
| `L1G.translate` family | partly possibly redundant | group-algebra file | Bare Lp-translation is `Lp.compMeasurePreserving`/`DomMulAct`; the new content is compatibility with convolution (`translate_mul`, `translateLp_mulCLM`). |
| `pairCLM` | skip | — | Local device; if upstreamed, factor as "multiplication by a bounded continuous function is a CLM on L¹". |
| `toLpCc_mconv_eq_integral` | upstream after changes | group-algebra file | Bochner-integral form `class (f ⋆ g) = ∫ a, f a • Lₐ(class g) ∂μ`; no Mathlib analog even additively. |
| `fourierTransform_separates`, `exists_fourierTransform_eq_one` | upstream as-is | LCA FourierTransform file | Nondegeneracy; needs only bumps upstream first. |
| `L1G.characterSpace_exists_char` | **upstream after changes — flagship** | new `…/LCA/CharacterSpace.lean` | Reviewers will want the bundled homeomorphism `PontryaginDual G ≃ₜ characterSpace ℂ (L¹ G)` (weak-* vs compact-open), with the `∃!` as corollary. |
| `NormedCommRing (WithLp 1 (Unitization ℂ (L1G μ)))` | upstream after changes | `Analysis/Normed/Algebra/UnitizationL1.lean` | Generalize to any `[NonUnitalNormedCommRing A]`; cheap, generally useful. |
| `unitizationInrCLM`, `toLp_inr_mul` | possibly redundant | — | Near-corollaries of `WithLp.unitization_isometry_inr` / `unitization_mul` (`UnitizationL1.lean:91`). |
| `L1G.npow` + lemmas | skip | — | Ad-hoc non-unital power; upstream phrasing should use `(inr F)^n` in the unitization (or pursue a generic `Pow A ℕ+` instance for non-unital semirings as a separate algebra PR). |
| `spectrum_unitization_subset`, `spectralRadius_unitization_le` | upstream after changes | `…/LCA/CharacterSpace.lean` | Restate in `quasispectrum` language (`Unitization.quasispectrum_eq_spectrum_inr`, `Quasispectrum.lean:349`). Factor out the missing generic lemma: *characters of a unitization = augmentation ⊔ characters of A* → `CharacterSpace`/GelfandDuality. |
| `exists_norm_npow_rpow_le` | upstream after changes | split: generic half near `GelfandFormula.lean`; L¹ half in CharacterSpace file | Generic: characters bounded by C on `a` ⇒ `limsup ‖aⁿ‖^(1/n) ≤ C` for non-unital commutative Banach algebras (via `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`, `GelfandFormula.lean:122`). |

### Pontryagin/FourierDense.lean (386 lines)

Density of C_c-transforms in C₀(Ĝ) + Fourier–Stieltjes uniqueness — *the* missing
uniqueness theorem for group harmonic analysis. Mathlib's charFun-based uniqueness
(`ext_of_integral_char_eq`, `Measure.ext_of_charFun`) is confined to complete
second-countable pseudo-EMetric vector spaces; the LCA statement is complementary.

| declaration | verdict | target | notes |
|---|---|---|---|
| `ccFourierC0` + lemmas | upstream after changes | `…/LCA/FourierStieltjes.lean` | Derive from `fourierC0` of the class to avoid two parallel bundlings. |
| `ccFourierSubalgebra` + membership | upstream after changes | same | Use `NonUnitalStarAlgHom.range` of `fourierHom` rather than a bespoke carrier. |
| `dense_ccFourierSubalgebra`, `exists_cc_fourier_close` | upstream as-is | same | Requires the C₀ Stone–Weierstrass PR first. Key theorem. |
| `ZeroAtInftyContinuousMap.norm_apply_le` | upstream as-is | `ZeroAtInfty.lean` | Genuinely absent convenience; generalize codomain. |
| `ZeroAtInftyContinuousMap.integrable` | possibly redundant | `Integral/BoundedContinuousFunction.lean` | One line via `v.toBCF.integrable` (`BoundedContinuousFunction.lean:99`); worth it only as dot-notation convenience. |
| `continuous_integral_zeroAtInfty` | upstream after changes | same | State for `→ᵇ` first (Mathlib has no continuity of `v ↦ ∫ v ∂σ` even there), derive C₀ version. |
| `Continuous.eq_zero_of_forall_integral_cc_eq_zero` | upstream as-is (rename) | with the AEEqOfIntegralCc file | Genuinely missing; generalize codomain; pairs with `Measure.ext_of_integral_eq_on_compactlySupported`. |
| `integral_fourierTransform_cc` | upstream as-is | `…/LCA/FourierStieltjes.lean` | Suggest also introducing a named `fourierStieltjes σ : G → ℂ := fun x => ∫ χ, χ x ∂σ` — three files pass this integral around unnamed. |
| `measure_ext_of_forall_integral_char_eq` | **upstream after changes — flagship** | same | Drop the spurious `include μ` (instantiate `Measure.haar` internally so the statement mentions only `G, σ₁, σ₂`); align naming with the charFun family. |

### Pontryagin/PositiveType.lean (717 lines)

Mathlib has **no positive-definite-function-on-a-group predicate** (grep verified:
only `Matrix.PosDef`/`PosSemidef`; `charFun` has no positive-definiteness lemma).
Prime, largely self-contained upstreaming material.

Definition-shape notes for the PR: the `Fin n`-sum definition in `ComplexOrder` is
faithful to the literature and pleasant to use; provide
`isPositiveType_iff_posSemidef` (matrix form) as a lemma, not the definition; ℂ →
`RCLike` is cheap for the algebraic layer, operator-valued (`StarOrderedRing`
algebra) is the eventual generality — ship ℂ first, stated so generalization is
nondisruptive; `@[to_additive]` works (only `G` is multiplicative); flag
`IsPositiveDefinite` as the alternative name for discoverability.

| declaration | verdict | target | notes |
|---|---|---|---|
| `IsPositiveType` | upstream after changes | new `Mathlib/Analysis/Fourier/PositiveDefinite.lean` | Def + algebraic theory needs only `[CommGroup G]`. |
| `apply_one_nonneg`, `apply_inv`, `norm_apply_le` | upstream as-is | same | Add the `‖f x‖ ≤ ‖f 1‖` corollary. |
| `isPositiveType_zero`, `.add`, `.smul_of_nonneg` | upstream as-is | same | Reviewers will ask for `conj`, Schur-product `mul`, pointwise-limit closure — cheap additions. |
| `isPositiveType_char`, `isPositiveType_integral_char` | upstream as-is | same / LCA file | The easy half of Bochner; hypotheses already minimal. |
| `isPositiveType_mconv_mstar(_of_memLp_two)` | upstream after changes | LCA file | Depends on the `mconvolution` layer. |
| `Continuous.exists_nhds_one_forall_norm_sub_le(_of_isCompact)` | upstream after changes | `Topology/Algebra/IsUniformGroup/Basic.lean` | ε-packaging of Heine–Cantor under a locally-installed group uniformity — not literally redundant (no uniformity-free statement exists); `@[to_additive]`; state in `dist` form. |
| `IsPositiveType.integral_mconv_nonneg`, `integral_mconv_mstar_mul_nonneg` | upstream as-is | LCA file | **The key bridge** (Riemann-sum argument, no product measures); technical heart of Bochner. |

### Pontryagin/Bochner.lean (1553 lines)

Bochner's theorem — absent from Mathlib in any form (only `charFun` uniqueness
exists, no existence/representation, nothing for groups). Highly upstreamable after
API redesign; several generic sub-lemmas deserve independent PRs, and one hidden
theorem should be factored out.

| declaration | verdict | target | notes |
|---|---|---|---|
| `Complex.isClosed_nonneg` | **redundant** | — | `Complex.orderClosedTopology` (`Analysis/Complex/Basic.lean:465`, scoped) makes it `isClosed_Ici`. Drop. |
| `complex_nonneg_of_forall_norm_sub_le` | skip | — | 3-line corollary of closedness; inline. |
| `ZeroAtInftyContinuousMap.exists_hasCompactSupport_norm_sub_le` | upstream after changes | `ZeroAtInfty.lean` / `CompactlySupported.lean` | C_c dense in C₀ — a known API gap; restate as `DenseRange` of the natural `C_c → C₀` map; generalize codomain. **High priority, fully independent.** |
| `IsCompact.exists_nhds_one_forall_norm_char_sub_one_le` | upstream after changes | `PontryaginDual.lean` | Equicontinuity of compact character sets; the general Ascoli converse is an explicit Mathlib TODO (`Ascoli.lean:61`) — cite it. |
| `posPairing` family | upstream after changes | new `Mathlib/Analysis/Fourier/LCA/Bochner.lean` | Minimize hypotheses; `Lp`-vs-synonym cleanup. |
| `norm_posPairing_mul_sq_le` (Cauchy–Schwarz) | possibly redundant | — | Derivable from `inner_mul_inner_self_le` (`InnerProductSpace/Basic.lean:282`) via a `PreInnerProductSpace.Core` value; or land the genuinely-missing abstract star-ring Cauchy–Schwarz (`‖φ(a⋆b)‖² ≤ (φ(a⋆a)).re (φ(b⋆b)).re`) first — Mathlib has it only inside C*-GNS. |
| `norm_posPairing_sq_le` | upstream after changes | LCA/Bochner | Uses the approximate identity; abstracting over "Banach *-algebra with bounded approximate identity" is blocked on Mathlib having no BAI API — keep concrete, note the TODO. |
| `norm_posPairing_le_fourier` | upstream after changes | LCA/Bochner | The classical "positive functional ≤ Gelfand transform" bound; the abstract Banach-*-algebra form is the reviewer-preferred target but needs new non-unital-character + BAI infrastructure — the concrete L¹(G) statement is the pragmatic path. Highest-value sub-lemma. |
| `bochnerCLM` family | upstream after changes | LCA/Bochner | Keep public; the square-root positivity trick is self-contained. |
| `continuous_integral_char` | upstream as-is | `…/LCA/FourierStieltjes.lean` | Continuity of `x ↦ ∫ χ, χ x ∂σ` via inner regularity + equicontinuity — the only proof that works on general Ĝ. High standalone value. |
| `bochnerRealC0`/`bochnerLambda`/`bochnerMeasure0`/`bochnerCLM_eq_integral` | upstream after changes (factor out) | new `MeasureTheory/Integral/RieszMarkovKakutani/ZeroAtInfty.lean` | Hidden theorem worth extracting: **every positive bounded functional on C₀(X, ℂ) is integration against a finite regular measure** — the complex RMK / C₀-dual gap. Wide independent value. |
| `IsPositiveType.exists_bochner_measure` | **upstream after changes — headline** | LCA/Bochner | Consider a `def IsPositiveType.bochnerMeasure` + instances instead of the bare existential. |
| `bochner_measure_unique`, `bochner_measure_mass` | upstream after changes | same | Drop the unused `hφ`/`μ` arguments (currently behind a linter opt-out — Mathlib will reject). |
| `integrable_coeFn_mul_posType`, `L1G.npow_mul_npow`, `L1G.star_npow` | skip | — | Trivial/synonym artifacts. |

### Pontryagin/Inversion.lean (1779 lines)

The dual Haar measure and Fourier inversion — the core of LCA Fourier analysis, all
absent from Mathlib (inversion exists only for finite-dimensional real inner-product
spaces; "dual Haar" greps to nothing).

| declaration | verdict | target | notes |
|---|---|---|---|
| `support_div_subset` | **redundant** | — | `Function.support_div` gives equality (`Algebra/GroupWithZero/Indicator.lean:146`). |
| `Continuous.div_of_tsupport_ne_zero` | upstream as-is (generalize) | `Topology/Algebra/Support.lean` | Junk-value quotient continuity; `GroupWithZero` + `HasContinuousInv₀` generality. |
| `Continuous.nonneg_of_forall_integral_cc_nonneg` | upstream as-is | `Integral/Bochner/Set.lean` | One-sided C_c testing; pairs with the eq-zero sibling. |
| char coercion/finite-measure basics (`continuous_char_apply`, `conj_char_apply`, `char_mul_conj_char`, `integrable_char`, `norm_integral_char_le`) | upstream as-is | `PontryaginDual.lean` / FourierStieltjes | Mathlib's PontryaginDual file is thin; these fill real gaps. |
| `integral_char_mul_fourierTransform` | upstream after changes | new `…/LCA/Inversion.lean` | The inverse-transform bridge `∫ χ(x)·𝓕f dσ = (f ⋆ σ̌)(x)`. |
| `integral_c0_mul_eq_of_forall_integral_char_mul_eq`, `integral_c0_mul_fourierTransform_symm` | upstream after changes | same | Density-form uniqueness + the symmetric identity (engine of dual-Haar well-definedness). |
| `fourierTransform_mconv_mstar` | upstream as-is | LCA FourierTransform file | `𝓕(g ⋆ g⋆) = ‖𝓕g‖²`. |
| `AdmissibleSquare` + its 13-lemma API | upstream after changes | new `…/LCA/DualHaar.lean` | Keep public but document as implementation of `dualHaar` (analogous to `haarContent`); make the `4⁻¹` constant a hypothesis or documented. |
| `dualSquare`, `dualLambda` glue | skip (private) | — | Choice-based RMK glue. |
| `dualHaar` + 5 instances + `integral_cc_dualHaar` etc. | **upstream after changes — headline** | `…/LCA/DualHaar.lean` | Should become THE canonical `MeasureTheory.Measure.dualHaar`. Reviewer asks to pre-empt: (a) scaling `dualHaar (c • μ) = c⁻¹ • dualHaar μ` (add it); (b) a Plancherel-normalization uniqueness lemma (any regular Haar ν with `f 1 = ∫ 𝓕f ∂ν` for one nonzero positive-type C_c f equals `dualHaar μ`); (c) consistency examples (compact G ↦ counting; the ℝ self-duality story vs `Real.fourierChar`). |
| `integral_cc_mul_fourierTransform_dualHaar` (density identity) | upstream after changes | same | The theorem that *defines* what `dualHaar` means. |
| `IsPositiveType.mstar_eq`, `fourierTransform_im` | upstream as-is | PositiveType/FourierTransform files | Small API. |
| `fourierTransform_re_nonneg`, `fourierTransform_eq_ofReal_re` + re-forms | upstream after changes | LCA/Inversion | `𝓕f ≥ 0` for Bochner-representable f; new. |
| `exists_cutoff_integral_ge` | upstream after changes (generalize) | `Measure/Regular.lean` or `Bochner/Set.lean` | Stated for the dual but fully generic (finite inner-regular measure on LCH Borel space): C_c cutoff with `∫ a ≥ σ(univ) − ε`. |
| integrability/mass/tail package (6 lemmas) | upstream after changes | LCA/Inversion | The super-level-set exhaustion works around non-σ-finiteness of `dualHaar` — exactly the generality Mathlib wants (Ĝ can be non-σ-compact). |
| `integral_bddContinuous_mul_fourierTransform_dualHaar` | upstream after changes | same | Restate with `BoundedContinuousFunction` instead of `(hvc, Cv, hvb)` triples. |
| `IsPositiveType.fourier_inversion`, `fourier_inversion_one` | **upstream after changes — headline** | `…/LCA/Inversion.lean` | Fourier inversion for positive-type L¹ functions; clean, hypothesis-minimal statements. |
| `exists_positiveType_cc_eq_one` | upstream as-is | PositiveType file | De-duplicate the bump-mass-positivity block shared with `exists_admissibleSquare` (factor `integral_normSq_bump_pos`). |

### Pontryagin/Plancherel.lean (1641 lines)

The L² theory. Broadly upstreamable; reviewers will demand the C_c-class
infrastructure be repackaged onto `CompactlySupportedContinuousMap` (which currently
has no `toLp` bridge at all).

| declaration | verdict | target | notes |
|---|---|---|---|
| `norm_sub_smul_div_max_le` | upstream after changes | `InnerProductSpace` (Basic or Projection) | Radial retraction onto a ball is nonexpansive toward ball points — **no metric projection onto convex sets/balls exists in Mathlib**. Generalize ℂ → real/RCLike inner-product space. Self-contained small PR. |
| `eLpNorm_two_le_ofReal`, `norm_toLp_two_sq`, `norm_toLp_two_eq_of_integral_sq_eq` | possibly redundant | `L2Space.lean` | Glue around `memLp_two_iff_integrable_sq_norm` (line 45); upstream at most as simp-friendly conveniences. |
| `exists_cc_close_L1_L2` | upstream after changes | `ContinuousMapDense.lean` | **Genuinely new**: simultaneous L¹∧L² C_c approximation. Generalize to arbitrary `p, q ≠ ∞` and codomain `E`. High value. |
| `integrable_mconv_integrand_L2` | skip | — | Travels with the convolution file. |
| `mconv_ae_eq_mulCLM` | upstream after changes | L¹-algebra file | Pointwise-convolution vs algebra-product consistency; restate against the final APIs. |
| C_c Parseval trio (`*_fourierTransform_cc`) | upstream as-is | `…/LCA/Plancherel.lean` | Clean. |
| `toLp2Cc` + `ccL2Submodule` + subtype plumbing (8 decls) | upstream after changes | via `CompactlySupportedContinuousMap.toLp` | Becomes `LinearMap.range` + `DenseRange`, matching how `Lp.fourierTransformₗᵢ` is built from `SchwartzMap.toLpCLM` (`Analysis/Fourier/LpSpace.lean`). |
| `funext_of_denseL2`, `ccRep2` family | skip | — | Density/choice plumbing; disappears under bundling. |
| `ccPlancherel*`/`plancherelCLM` intermediates | upstream after changes | Plancherel file | Construct via the isometry-extension idiom. |
| `plancherelLI` + agreement | **upstream after changes — headline** | Plancherel file | Package as `plancherelₗᵢ : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 (dualHaar μ)` via `LinearIsometryEquiv.ofSurjective` (precedent `InnerProductSpace/Dual.lean:136`); hook into the `FourierTransform`/`𝓕` notation classes (`Analysis/Fourier/Notation.lean:36,226`); provide the `symm`-direction agreement; the `dualHaar` normalization lemmas above are prerequisites reviewers will demand. |
| `memLp_two_fourierTransform`, `plancherelLI_memLp_toLp`, `integral_norm_sq_fourierTransform` | upstream as-is | Plancherel file | **Parseval on L¹∩L²** — the citable statement; the LCA analogue of `Lp.norm_fourier_eq` with an honest pointwise representative. High value. |
| `ae_eq_zero_of_forall_integral_char_mul_eq_zero` | upstream as-is | Uniqueness/Plancherel file | Dual L¹-uniqueness; no Mathlib analogue at any generality; also the key to `eval_surjective`. |
| `surjective_plancherelLI` | upstream as-is (then merge into `≃ₗᵢ`) | Plancherel file | Rename `plancherelLI_surjective`. |
| `fourierTransform_conj_mul_char` | upstream as-is | LCA FourierTransform file | Algebra lemma; wrong file currently. |
| `exists_integrable_fourierTransform_eq_zero_compl` | upstream as-is | Plancherel file | Localized transforms; consider recording `Continuous (𝓕Φ)` in the conclusion (free). |

### Pontryagin/EvalInjective.lean (270), Pontryagin/Duality.lean (125), Pontryagin/Basic.lean (143)

**The headline Mathlib target.** Verified: Mathlib's `PontryaginDual.lean` docstring
explicitly describes Pontryagin duality as the motivating example, and the file
contains no `eval` and no duality.

| declaration | verdict | target | notes |
|---|---|---|---|
| `PontryaginDual.eval` + `eval_apply` (Basic) | upstream as-is | **existing** `Mathlib/Topology/Algebra/PontryaginDual.lean` | Needs only `[LocallyCompactSpace A]`, no analysis. Trivial, immediately mergeable first PR. |
| `evalInvOfBijectiveOfIsOpenMap` (Basic) | skip | — | Superseded by `toDoubleDual`; Mathlib has `toHomeomorphOfIsInducing`. |
| finite `dualityEquiv` + `card_dual` + `equivAddChar` (Basic) | upstream after changes | `Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean` | Genuinely new (Mathlib's `AddChar.doubleDualEquiv` is algebraic, ℂ-valued, never touches `PontryaginDual`). Make the private bridges public — `card (PontryaginDual A) = card A` is independently useful. Later add `dualityEquiv = toDoubleDual` as a consistency lemma. |
| `eval_injective_aux` / `isInducing_eval_aux` (EvalInjective) | upstream as-is (merged) | `…/LCA/PontryaginDuality.lean` | Fold the `_aux` split away. The borel-σ-algebra-inside-the-proof idiom is accepted Mathlib style — exact precedent `MeasureTheory/Group/ModularCharacter.lean:46`. Add the citable corollary `exists_pontryaginDual_ne_one : z ≠ 1 → ∃ χ, χ z ≠ 1`. |
| `eval_injective`, `isInducing_eval`, `isEmbedding_eval`, `isClosed_range_eval`, `eval_surjective`, `eval_bijective` | upstream as-is | same | All measure-free — the selling point. `isClosed_range_eval` needs the Topology.lean subgroup lemma first. |
| `toDoubleDual` + `toDoubleDual_apply` | **upstream after changes — THE headline** | same | Propose `PontryaginDual.doubleDualEquiv : G ≃ₜ* PontryaginDual (PontryaginDual G)` (mirroring `AddChar.doubleDualEquiv`). Add API: `symm_apply`, naturality vs `PontryaginDual.map` (`map (map f) ∘ eval = eval ∘ f`), `IsOpenMap eval`. File: `Analysis/Fourier/LCA/PontryaginDuality.lean` (precedent: the FiniteAbelian file); update the `PontryaginDual.lean` docstring to point at it. |

### Non-proof items

- `Solution.lean` / `Challenge.lean` / `config.json` — comparator artifacts; skip
  (Mathlib gets `toDoubleDual` directly; the existential phrasing is an anti-pattern there).
- `Pontryagin/Minimum.lean` — empty leftover placeholder; delete from the repo.
- `Pontryagin.lean` — import umbrella; replaced by the Mathlib file hierarchy.
- `PLAN.md` — distill its deviation notes into the module docstrings of the upstream
  files; its `NormalSpace` watch-out should be re-verified against current Mathlib
  when preparing that PR (see Density section).
- `README.md`, `.github/` — repository-specific; no upstream relevance.
- `data/pontryagin_duality_mathlib.{tex,pdf}` — ideal companion material for the PR
  series description or a blueprint project page; not itself a Mathlib artifact.
- `blueprint/` — could accompany the upstreaming as a public progress page; not a PR.

---

## Do not upstream (redundancies found, with citations)

| project declaration | Mathlib fact that covers it |
|---|---|
| `integral_integral_swap_of_continuous_compactSupport` | `MeasureTheory.integral_integral_swap_of_hasCompactSupport` (`Integral/Prod.lean:602`, already curried) |
| `cc_rep_unique` | `Continuous.ae_eq_iff_eq` (`Measure/OpenPos.lean:141`) |
| `Complex.isClosed_nonneg` | scoped `Complex.orderClosedTopology` (`Analysis/Complex/Basic.lean:465`) + `isClosed_Ici` |
| `support_div_subset` | `Function.support_div` (`Algebra/GroupWithZero/Indicator.lean:146`, an equality) |
| `measurePreserving_inv_mul` | `measurePreserving_div_left` (`Group/Measure.lean:387`) |
| `translateLp` + its lemma set, `continuous_translateLp` | `Lp.compMeasurePreservingₗᵢ` (`LpSpace/Basic.lean:630`); `DomMulAct` action + `Lp.instContinuousSMulDomMulAct` (`LpSpace/DomAct/Continuous.lean:53` — jointly continuous, weaker hypotheses) |
| `norm_sub_eq_integral` | `L1.norm_eq_integral_norm` (`Integral/Bochner/Basic.lean:904`) + `Lp.coeFn_sub` |
| `Circle.norm_coe_sub_one_le_abs_arg` (as proved) | `Complex.norm_exp_I_mul_ofReal_sub_one_le` (`Trigonometric/Bounds.lean:260`) + `Circle.exp_arg` |
| `unitizationInrCLM`, `toLp_inr_mul` | `WithLp.unitization_isometry_inr` / `unitization_mul` (`UnitizationL1.lean:91`) |
| `ZeroAtInftyContinuousMap.integrable` (as new content) | `BoundedContinuousFunction.integrable` (`Integral/BoundedContinuousFunction.lean:99`) via `toBCF` |
| `norm_posPairing_mul_sq_le` (as bespoke proof) | `inner_mul_inner_self_le` (`InnerProductSpace/Basic.lean:282`) via `PreInnerProductSpace.Core` |

---

## Cross-cutting changes required before any PR

1. **Linter opt-outs must go.** Every file uses coarse hypothesis blocks under
   `set_option linter.unusedSectionVars false` (and some `linter.style.show false`);
   Mathlib requires per-lemma minimal typeclasses. Many lemmas need only
   `IsMulLeftInvariant` or `IsInvInvariant`, not `IsHaarMeasure + Regular`.
2. **`maxHeartbeats` bumps** (four in Plancherel.lean) need proof-splitting or
   per-declaration scoping.
3. **Bundle C_c**: introduce `CompactlySupportedContinuousMap.toLp` and route all
   `toLpCc`/`ccRep`/`ccSubmodule` machinery through it.
4. **Names**: `mconv` clashes with `Measure.mconv`; `L1G` and `norm_L1_*` are not
   Mathlib-style; align the Fourier definitions with the `fourierIntegral` family and
   the uniqueness theorems with the `charFun`/`ext_of_integral_char_eq` family.
5. **Generalize scalars** where free: ℂ → `RCLike` (algebraic layers), codomains to
   Banach spaces (transform, C₀ helpers).
6. **`@[to_additive]`** on everything where only `G` is multiplicative (subgroup
   closedness, translate, positive-definite functions, uniform-continuity helpers);
   the `PontryaginDual`-valued stack is legitimately multiplicative-only.
7. **Convention reconciliation** with `VectorFourier.fourierIntegral` via the
   `(χ x)⁻¹ • f x` form and an explicit compatibility lemma.

---

## Consolidated PR roadmap

Dependency-ordered; each wave is independently valuable and reviewable.

**Wave 0 — leaf lemmas (independent, small, land first).**
1. `IsLocallyClosed.of_locallyCompactSpace` + `Subgroup.isClosed_of_locallyCompactSpace`
   (+ factored `isClosed_of_isLocallyClosed`, `to_additive`).
2. `PontryaginDual.eval` + `eval_apply` into the existing PontryaginDual file.
3. C₀ ↔ OnePoint embedding API; then Stone–Weierstrass for C₀ (cite Mathlib's
   "Future work" note).
4. C_c dense in C₀ (`DenseRange` form); C_c testing lemmas
   (`ae_eq_zero_of_forall_integral_mul_eq_zero`, one-sided variant, quantitative L¹ bound).
5. Circle arc lemmas (closure, generalized power control); CompactOpen refactor
   (`isCompact_setOf_mapsTo`) + `PontryaginDual` polars/nhds basis/`ContinuousEvalConst`.
6. CcFubini slice/partial-integral API; the finite-measure one-variable-compact-support
   Fubini; the generalized cutoff lemma `exists_cutoff_integral_ge`.
7. The ball-clamp projection inequality (inner-product spaces).
8. `NormedCommRing (WithLp 1 (Unitization 𝕜 A))` for commutative A; the
   "characters of a unitization" classification.
9. Positive-definite functions: `IsPositiveType` + algebraic theory + characters
   (have the definitional bikeshedding here, before dependent material).
10. The factored complex Riesz representation: positive bounded functionals on
    C₀(X, ℂ) are finite regular measures (`RieszMarkovKakutani/ZeroAtInfty.lean`).

**Wave 1 — density and measure infrastructure.**
11. The `ContinuousMapDense` hypothesis fix (`RegularSpace + LocallyCompactSpace`),
    generalized to `E`; `CompactlySupportedContinuousMap.toLp` + `toLp_denseRange`;
    the simultaneous `L^p ∧ L^q` approximation.
12. Multiplicative translate (`to_additive`-ize `Translate.lean`) + generalized
    normalized bumps.

**Wave 2 — convolution and the L¹ algebra.**
13. `mconvolution` (bilinear-`L`, `to_additive` where possible) + `mstar` + the C_c
    lemma set + **Young's L¹ bound** + the **L²×L² bound/continuity** (closes
    Convolution.lean's TODO).
14. The L¹(G) Banach *-algebra with approximate identity (the design-review PR).

**Wave 3 — the Fourier layer.**
15. LCA `fourierIntegral` + algebra identities + continuity + **Riemann–Lebesgue**;
    compatibility lemma with `VectorFourier`.
16. `fourierHom` into C₀; separation/nonvanishing; density of transforms;
    **Fourier–Stieltjes uniqueness**; a named `fourierStieltjes`.
17. The spectrum theorem as `PontryaginDual G ≃ₜ characterSpace ℂ (L¹ G)`;
    quasispectrum restatement of the unitization bound; the Gelfand-formula corollary.

**Wave 4 — the analytic headliners.**
18. **Bochner's theorem** (`…/LCA/Bochner.lean`), with the Cauchy–Schwarz step routed
    through `PreInnerProductSpace.Core` or a new abstract star-ring lemma.
19. **`Measure.dualHaar`** + Haar instances + density identity + scaling +
    normalization-uniqueness; **Fourier inversion**.
20. **Plancherel** as `plancherelₗᵢ : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 (dualHaar μ)` +
    Parseval + dual L¹-uniqueness + localized transforms + `𝓕`-notation instances.

**Wave 5 — the theorem.**
21. `…/LCA/PontryaginDuality.lean`: `eval_injective`, `isInducing_eval`,
    `isClosed_range_eval`, `eval_surjective`, **`doubleDualEquiv`** — all
    measure-free — plus naturality API, the finite-case consistency lemma, and the
    docstring update in `PontryaginDual.lean`.

Expected review friction concentrates in three places: the `ContinuousMapDense`
hypothesis change (11), the L¹-algebra packaging (14), and the `dualHaar`
normalization API (19). Everything in Wave 0 should be low-controversy, and several
items there (Stone–Weierstrass for C₀, the Ascoli-converse equicontinuity lemma, the
Convolution TODOs) respond to requests already written down in Mathlib's own source.

# Formalization plan: Pontryagin duality for LCA groups

Goal: remove the three `sorry`s in [Pontryagin/Duality.lean](Pontryagin/Duality.lean)
(`eval_injective`, `isInducing_eval`, `eval_surjective`). Everything else —
the closed-range step, the final `toDoubleDual` assembly, and `Solution.lean` — is done
and builds.

Reference: the proof blueprint in `data/pontryagin_duality_mathlib.tex`, **with the
deviations recorded below** (chosen after a full inventory of Mathlib v4.32.0).

## Architecture deviations from the blueprint

1. **Bochner via positive functionals, not GNS.** Mathlib has no spectral theorem for
   bounded normal operators, no projection-valued measures, no analytic Schur lemma —
   but full Gelfand theory (`WeakDual.characterSpace`, Gelfand–Mazur, spectral radius).
   So Bochner's theorem is proved the Naimark/Loomis way:
   positive-type φ ↔ positive functional `T f = ∫ f·φ` on L¹(G);
   Cauchy–Schwarz + iteration `T(g) ≤ ‖φ‖^(1-2⁻ⁿ)·T(g^(2ⁿ))^(2⁻ⁿ)` + spectral radius
   formula gives `|T f| ≤ φ(1)·‖f̂‖_∞`; transport T through the Fourier transform to a
   positive functional on a dense subalgebra of C₀(Ĝ), extend, restrict to C_c, apply
   Mathlib's positive Riesz–Markov (`rieszMeasure`). No Krein–Milman, no Banach–Alaoglu,
   no GNS, no extreme points needed.
   - Characters-are-extreme is not needed at all in this route.
   - The needed spectral radius facts live at the unitization of L¹(G):
     characters of `Unitization ℂ (L¹ G)` = characters of L¹(G) plus the point at
     infinity (manual classification), and `spectrum.gelfandTransform_eq`-style results.

2. **No complex measures.** Mathlib's `VectorMeasure`/complex-RMK API is too thin.
   Every "finite complex measure" of the blueprint is reformulated as *equalities of
   integrals of bounded complex densities against finite positive measures*, and
   inversion (§8) is developed **only for positive-type f ∈ L¹** (that is all the
   duality proof uses; σ_f is then a positive measure, and `ê_U = |ĥ_U|² ≥ 0`,
   `f̂ ≥ 0` come for free). Key reformulations:
   - FS-uniqueness (positive form): finite positive regular σ₁, σ₂ on Ĝ with
     `∫ χ(x) dσ₁ = ∫ χ(x) dσ₂` for all x ⇒ σ₁ = σ₂
     (Fubini + Stone–Weierstrass-density of transforms in C₀ +
     `Measure.ext_of_integral_eq_on_compactlySupported`).
   - FS-uniqueness (density form): w ∈ L¹(σ;ℂ), σ finite regular,
     `∫ χ(x)·w dσ = 0` ∀x ⇒ w = 0 σ-a.e. (test against C_c via regularity of σ).
   - Symmetric measure identity as `∀ a ∈ C_c(Ĝ): ∫ a·ĝ dσ_f = ∫ a·f̂ dσ_g`.
   - Dual Haar functional: `Λ γ := ∫ (γ/ê_U) dσ_{e_U}` for any U with `ê_U > 1/2` on
     supp γ (well-defined by the symmetric identity), positive, translation-invariant
     ⇒ `μ_Ĝ := rieszMeasure Λ`; invariance + nontriviality ⇒ `IsOpenPosMeasure`.

3. **C_c-first, density extension — no product σ-algebras at all.** Two obstructions
   kill any `Measure.prod` route on general LCA groups: Haar on a non-σ-compact group
   is not s-finite (Mathlib Fubini needs `SFinite`), and — worse — on
   non-second-countable groups even the continuous kernel `(x,y) ↦ g (y⁻¹ * x)` need
   not be product-σ-algebra measurable (this is why Mathlib's `Group/Prod.lean` demands
   `MeasurableMul₂`). Note Ĝ can be non-σ-compact even for compact G (e.g. `Circle^I`),
   so σ-compactness hypotheses can't be discharged by reduction. The classical fix
   (Hewitt–Ross): prove every convolution identity for **continuous compactly
   supported** functions, where the iterated-integral swap is elementary — approximate
   a jointly continuous compactly supported kernel `F : X × Y → ℂ` uniformly by finite
   sums `Σ φᵢ(x)·F(zᵢ,y)` (uniform continuity + finite cover + continuous partition of
   unity), for which the swap is trivial — then extend all operations and identities to
   L¹ by density and bilinear continuity. Pointwise convolution formulas are only ever
   used for C_c functions and for L²×L² (where slice-wise Cauchy–Schwarz needs no
   product measure). Consistency of the L¹ extension with pointwise formulas is
   obtained through simultaneous C_c approximation in (L¹, L²) or (L¹, sup) norms.

4. **Multiplicative convolution defined in-project.** Mathlib's Bochner convolution is
   additive-only; `Additive G` transport would poison every character statement. Define
   `mconv μ f g x = ∫ y, f y * g (y⁻¹ * x) ∂μ` for `f g : G → ℂ` and prove the ~10
   needed lemmas (mirroring `Mathlib/Analysis/Convolution.lean` proofs).

## File/layer map (all under `Pontryagin/`, imported by `Solution.lean`)

| file | contents | status |
|---|---|---|
| `Basic.lean` | `eval`, `eval_apply`, inverse-from-bijective-open; finite case | ✅ done (pre-existing) |
| `Topology.lean` | loc. compact subspace of T2 is locally closed; loc. compact subgroup closed | ✅ done |
| `Duality.lean` | 3 core sorries + closed range + `toDoubleDual` assembly | ✅ skeleton builds |
| `CcFubini.lean` | iterated-integral swap for jointly continuous compactly supported kernels on X × Y (LCH spaces, Radon measures), via uniform continuity + finite covers + continuous partitions of unity | ⬜ next |
| `Convolution.lean` | pointwise `mconv μ f g x = ∫ y, f y * g (y⁻¹ * x) ∂μ` used only on C_c×C_c and L²×L²; `star` involution `f^*(x) = conj (f x⁻¹)`; for C_c: membership in C_c, support lemma, ‖·‖₁-bound, comm, assoc, star identities (via CcFubini); for L²×L²: sup bound + continuity (slice-wise, no Fubini) | ⬜ |
| `ApproximateIdentity.lean` | normalized C_c bumps on identity nbhds; translation continuity in Lp (from `Lp.compMeasurePreserving` + `DomMulAct` instance); `h_U ⋆ f → f` in L¹; `ĥ_U → 1` uniformly on compacts | ⬜ |
| `L1Algebra.lean` | type synonym for `Lp ℂ 1 μ` with `NormedRing` whose multiplication is the **density extension** of C_c convolution (assoc/comm/norm-bound extend by continuity), `NormedAlgebra ℂ`, `StarRing`, `CompleteSpace`; unitization norm if Mathlib lacks a Banach-algebra `Unitization` norm | ⬜ |
| `FourierTransform.lean` | `𝓕 f χ = ∫ f x * conj (χ x) ∂μ`: bounded, continuous, `∈ C₀(Ĝ)` (Riemann–Lebesgue), multiplicative on convolution, star/translation/modulation identities | ⬜ |
| `Spectrum.lean` | every character of L¹(G) is `f ↦ 𝓕 f χ` for a unique χ (translation-ratio argument, Bochner-integral identity `f ⋆ g = ∫ f a • L_a g da`); spectral radius `r(f) = ‖𝓕 f‖_∞` via unitization | ⬜ |
| `StoneWeierstrassC0.lean` | Stone–Weierstrass for C₀ of a locally compact T2 space via one-point compactification (absent from Mathlib) | ⬜ independent |
| `PositiveType.lean` | finite-sum positive-definite def; elementary bounds; characters & `g ⋆ g^*` are positive-type; integral criterion; ↔ positive functional on L¹ | ⬜ |
| `Bochner.lean` | route of deviation 1: `φ(x) = ∫ χ(x) dσ_φ`, σ_φ finite positive regular, `σ_φ(Ĝ) = φ(1)`; uniqueness | ⬜ |
| `Inversion.lean` | `e_U = h_U ⋆ h_U^*`; symmetric identity; dual Haar `μ_Ĝ`; inversion for positive-type L¹ functions; `f̂ ≥ 0`, `∫ f̂ dμ_Ĝ = f 1` | ⬜ |
| `Plancherel.lean` | Parseval on L¹∩L²; range dense; unitary `𝒫`; `𝓕(a·b) = 𝒫a ⋆ 𝒫b`; localized transform in any nonempty open ⊆ Ĝ | ⬜ |
| `DualityProof.lean` | fill the three sorries: injectivity (inversion of a convolution square), inducing (compact polars via `∫ f̂ = 1` tail estimate), surjectivity (localized transform on Ĝ misses the closed range ⇒ FS-uniqueness contradiction) | ⬜ |

Dependency spine: CcFubini → Convolution → {ApproximateIdentity, L1Algebra} →
FourierTransform → Spectrum → (+ StoneWeierstrassC0) → {FS-uniqueness in Bochner.lean}
→ PositiveType → Bochner → Inversion → Plancherel → DualityProof.
Note the whole analytic stack must apply to **Ĝ** as well as G (surjectivity uses
localized transforms on Ĝ), so every lemma is stated for a general LCA group + Haar.

## Mathlib inventory digest (v4.32.0, verified against local checkout)

**Have:** `PontryaginDual` + LCS/compact/discrete instances + `map`; Circle
`centeredArc` basis + no-small-subgroups; Arzelà–Ascoli; `ContinuousMonoidHom`
compact-open API (`continuous_of_continuous_uncurry`, `ContinuousEval`); Haar
(regular, inv-invariant on abelian, `IsOpenPosMeasure`, uniqueness σ-finite);
`Lp.compMeasurePreserving` + `DomMulAct` translation continuity (needs only
`InnerRegularCompactLTTop`, no σ-finiteness); C_c dense in Lp (`μ.Regular`); Urysohn
bumps (`exists_continuous_one_zero_of_isCompact`); `HasCompactSupport.uniformContinuous_of_continuous`;
Bochner integral into Banach spaces + `integral_comp_comm`; positive Riesz–Markov
(NNReal + Real `→ₚ`) with `rieszMeasure`, `integral_rieszMeasure`,
`Measure.ext_of_integral_eq_on_compactlySupported`; Gelfand: `characterSpace`,
`norm_le_norm_one`, `CompactSpace (characterSpace ℂ A)` (unital complete),
`gelfandTransform`, Gelfand–Mazur; Krein–Milman & Banach–Alaoglu (not needed in new
route); `L2` inner product; compact-open `isOpen_setOf_mapsTo`; quotient group
instances; finite-abelian duality; `IsEmbedding.toHomeomorph`;
`MulEquiv.toContinuousMulEquiv`.

**Missing (we build):** multiplicative Bochner convolution + Young; L¹ Banach
algebra structure; positive-definite functions + Bochner; complex RMK / C₀-dual;
L¹–L∞ duality (avoided); Stone–Weierstrass for C₀; LCA Fourier transform/inversion/
Plancherel; compact lifting through quotients (not needed in new route); spectral
theorem for normal operators (avoided); Fubini without s-finiteness (worked around).

## Watch-outs

- Filter dominated convergence in Mathlib needs `IsCountablyGenerated`; the identity-
  neighborhood net is not. All approximate-identity limits must be explicit ε-estimates.
- Strong measurability of Banach-valued maps (e.g. `a ↦ f a • L_a g`) needs separable
  range: restrict to the σ-compact support first.
- `Solution.lean` must stay sorry-free-checkable: final theorem must use only axioms
  `propext, Quot.sound, Classical.choice` (no `native_decide`).
- Comparator requires the `Challenge.lean` statement to elaborate identically —
  never touch `Challenge.lean`, `config.json`, `lakefile.toml`, `lean-toolchain`.
- Check axioms at the end with `#print axioms pontryagin_duality`.

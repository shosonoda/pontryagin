import Verso
import VersoManual
import VersoBlueprint
import Pontryagin.Spectrum
import Pontryagin.UnitizationSpectrum
import Pontryagin.FourierDense

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The spectrum of L¹" =>

Gelfand theory enters here: the characters of the commutative Banach algebra
$`L^1(G)` are exactly the evaluations of the Fourier transform at points of
$`\hat{G}`. Together with the spectral radius formula (through the unitization)
this yields the fundamental sup-norm bound used by the Bochner layer, and with
Stone–Weierstrass it yields density of transforms in $`C_0(\hat{G})` and the
uniqueness theorem for Fourier–Stieltjes transforms.

:::group "spectrum"
The Gelfand spectrum of $`L^1(G)`: character classification, spectral radius
bounds through the unitization, density of transforms in $`C_0(\hat{G})`, and
Fourier–Stieltjes uniqueness.
:::

:::definition "l1_fourier_hom" (parent := "spectrum") (lean := "MeasureTheory.L1G.fourier, MeasureTheory.L1G.fourierHom")
**The Fourier transform on $`L^1` classes.** `L1G.fourier μ F` is the Fourier
transform of an $`L^1` class; by {uses "fourier_continuous"}[] and
{uses "riemann_lebesgue"}[] it lands in $`C_0(\hat{G}, \mathbb{C})`, and by
{uses "fourier_mconv"}[] (extended by density from $`C_c`) the bundled map
`L1G.fourierHom μ : L1G μ →⋆ₙₐ[ℂ] C₀(Ĝ, ℂ)` is a homomorphism of non-unital star
algebras on {uses "l1_algebra_def"}[].
:::

:::theorem "fourier_separates" (parent := "spectrum") (lean := "PontryaginDual.fourierTransform_separates")
**Separation.** Distinct characters $`\chi \neq \chi'` of $`G` are separated by
the Fourier transform of some continuous compactly supported function:
$`\widehat{f}(\chi) \neq \widehat{f}(\chi')`.
:::

:::proof "fourier_separates"
Pick $`x` with $`\chi(x) \neq \chi'(x)` and a small bump $`h` near $`x`
({uses "normalized_bump" (intent := "auxiliary")}[]); the transform
({uses "fourier_def"}[]) of $`h` times a character evaluates the two characters
differently.
:::

:::theorem "fourier_nonvanishing" (parent := "spectrum") (lean := "PontryaginDual.exists_fourierTransform_eq_one")
**Non-vanishing.** For every character $`\chi \in \hat{G}` there is a continuous
compactly supported $`f` with $`\widehat{f}(\chi) = 1`; the transform does not
vanish identically at any point of the dual.
:::

:::proof "fourier_nonvanishing"
Take a normalized bump $`h` ({uses "normalized_bump"}[]) and set
$`f = h \cdot \chi`; modulation becomes translation in the dual
({uses "fourier_def"}[]), so $`\widehat{f}(\chi) = \widehat{h}(1) = \int h = 1`.
:::

:::theorem "character_classification" (parent := "spectrum") (lean := "MeasureTheory.L1G.characterSpace_exists_char")
**Character classification.** Every character $`\varphi` of the Banach algebra
$`L^1(G)` is evaluation of the Fourier transform at a unique point of the
Pontryagin dual: there is a unique $`\chi \in \hat{G}` with
$`\varphi(F) = \widehat{F}(\chi)` for all $`F \in L^1(G)`.
:::

:::proof "character_classification"
The translation-ratio argument: for $`\varphi(F) \neq 0` the map
$`x \mapsto \varphi(\tau_x F) / \varphi(F)` is a continuous character $`\chi` of
$`G`, independent of $`F`, and testing against the approximate identity
{uses "approx_identity"}[] identifies $`\varphi` with
$`F \mapsto \widehat{F}(\chi)` via {uses "l1_fourier_hom"}[]. Uniqueness is
{uses "fourier_separates"}[].
:::

:::theorem "spectrum_unitization" (parent := "spectrum") (lean := "MeasureTheory.L1G.spectrum_unitization_subset")
**Spectra through the unitization.** In the unital commutative Banach algebra
$`\mathrm{WithLp}\ 1\ (\mathrm{Unitization}\ \mathbb{C}\ (L^1 G))`, the spectrum
of $`F \in L^1(G)` is contained in
$`\{0\} \cup \mathrm{range}(\widehat{F})`.
:::

:::proof "spectrum_unitization"
Every unital character of the unitization either kills $`L^1(G)` (the
augmentation, contributing $`0`) or restricts to a character of $`L^1(G)`, which
is evaluation of the transform by {uses "character_classification"}[]; Gelfand
theory identifies the spectrum with the character values.
:::

:::theorem "gelfand_bound" (parent := "spectrum") (lean := "MeasureTheory.L1G.exists_norm_npow_rpow_le")
**The spectral-radius bound.** If
$`\lVert \widehat{F} \rVert_\infty \le C`, then for every $`\varepsilon > 0` and
all large $`n`,
$`\lVert F^{n+1} \rVert^{1/(n+1)} \le C + \varepsilon`
(convolution powers in $`L^1(G)`). This is the Gelfand spectral radius formula in
the exact unitization-free shape consumed by the Bochner layer.
:::

:::proof "gelfand_bound"
By {uses "spectrum_unitization"}[] the spectral radius of $`F` in the unitization
is at most $`C`; the Gelfand formula
$`\rho(F) = \lim \lVert F^n \rVert^{1/n}` transfers the bound to convolution
powers.
:::

:::theorem "fourier_dense" (parent := "spectrum") (lean := "PontryaginDual.dense_ccFourierSubalgebra")
**Density of transforms.** The Fourier transforms of continuous compactly
supported functions form a dense non-unital star subalgebra
`ccFourierSubalgebra μ` of $`C_0(\hat{G}, \mathbb{C})`.
:::

:::proof "fourier_dense"
The set of transforms is a star subalgebra by {uses "fourier_mconv"}[] and the
star identity; it separates points by {uses "fourier_separates"}[] and vanishes
nowhere by {uses "fourier_nonvanishing"}[], so
{uses "stone_weierstrass_c0"}[] applies.
:::

:::theorem "fs_uniqueness" (parent := "spectrum") (lean := "PontryaginDual.measure_ext_of_forall_integral_char_eq")
**Fourier–Stieltjes uniqueness (positive form).** Two finite positive regular
measures $`\sigma_1, \sigma_2` on $`\hat{G}` with
$`\int_{\hat{G}} \chi(x)\, d\sigma_1(\chi) = \int_{\hat{G}} \chi(x)\, d\sigma_2(\chi)`
for every $`x \in G` are equal. This positive-measure reformulation replaces all
uses of complex measures in the classical blueprint.
:::

:::proof "fs_uniqueness"
The Fubini theorem {uses "finite_measure_fubini"}[] converts the hypothesis into
equality of integrals $`\int \widehat{f}\, d\sigma_1 = \int \widehat{f}\, d\sigma_2`
for all $`C_c` functions $`f`; by {uses "fourier_dense"}[] this extends to all of
$`C_0(\hat{G})`, and Mathlib's
`Measure.ext_of_integral_eq_on_compactlySupported` concludes.
:::

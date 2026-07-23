import Verso
import VersoManual
import VersoBlueprint
import Pontryagin.Inversion

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The dual Haar measure and Fourier inversion" =>

This chapter constructs a Haar measure on the dual group $`\hat{G}` out of the
Bochner measures of convolution squares, and proves the Fourier inversion formula
for continuous integrable functions of positive type. Everything is phrased with
positive measures only: the classical "inverse Fourier transforms of complex
measures" are systematically replaced by integrals of bounded continuous
densities against finite positive Bochner measures, and inversion is developed
exactly for the positive-type $`L^1` functions the duality proof needs.

:::group "inversion"
Admissible convolution squares, the dual Haar measure via Riesz–Markov, the
density identity, and the Fourier inversion formula for positive-type functions.
:::

:::definition "admissible_square" (parent := "inversion") (lean := "MeasureTheory.AdmissibleSquare")
**Admissible squares.** For a compact $`K \subseteq \hat{G}`, an
`AdmissibleSquare μ K` is a bundle: a convolution square
$`e = h \star h^*` of a continuous compactly supported function (hence of
positive type by {uses "conv_square_positive_type"}[], with
$`\widehat{e} = \lvert \widehat{h} \rvert^2 \ge 0`), its Bochner measure
$`\sigma_e` from {uses "bochner"}[], and the lower bound
$`\widehat{e} \ge 1/4` on $`K`.
:::

:::theorem "exists_admissible_square" (parent := "inversion") (lean := "MeasureTheory.exists_admissibleSquare")
For every compact $`K \subseteq \hat{G}` there exists an admissible square
({uses "admissible_square"}[]) for $`K`.
:::

:::proof "exists_admissible_square"
By {uses "bump_fourier_close"}[], a normalized bump $`h` supported near $`1` has
$`\widehat{h}` uniformly close to $`1` on $`K`, so
$`\widehat{e} = \lvert \widehat{h} \rvert^2 \ge 1/4` on $`K`.
:::

:::definition "dual_haar" (parent := "inversion") (lean := "MeasureTheory.dualHaar")
**The dual Haar measure.** The positive functional
$`\Lambda(\gamma) = \int_{\hat{G}} \gamma(\chi) / \mathrm{Re}\,\widehat{e}(\chi)\ d\sigma_e(\chi)`
on $`C_c(\hat{G}, \mathbb{R})` — for any admissible square $`e` for
$`\operatorname{tsupport} \gamma`, well-defined by the symmetric identity
(`AdmissibleSquare.pairing_congr`) — yields, via Riesz–Markov–Kakutani, the
measure `dualHaar μ` on $`\hat{G}`. It depends on
{uses "exists_admissible_square"}[].
:::

:::theorem "dual_haar_is_haar" (parent := "inversion") (lean := "MeasureTheory.dualHaar_isHaarMeasure, MeasureTheory.dualHaar_regular, MeasureTheory.dualHaar_isMulLeftInvariant")
The measure {uses "dual_haar"}[] is a regular Haar measure on $`\hat{G}`: it is
regular by construction, translation invariant, nonzero, and positive on open
sets.
:::

:::proof "dual_haar_is_haar"
Translation invariance follows from the modulation action on admissible squares
(`AdmissibleSquare.mulChar`: translating a character amounts to multiplying the
square by a character, which acts on the Bochner measure by translation).
Nontriviality comes from evaluating the defining functional on a transform of a
bump; invariance plus nontriviality forces `IsOpenPosMeasure`.
:::

:::theorem "density_identity" (parent := "inversion") (lean := "MeasureTheory.integral_cc_mul_fourierTransform_dualHaar")
**The density identity.** For $`f` continuous, integrable, of positive type with
Bochner measure $`\sigma_f`, and every $`a \in C_c(\hat{G}, \mathbb{C})`:
$`\int_{\hat{G}} a\, \widehat{f}\ d(\mathrm{dualHaar}\ \mu) = \int_{\hat{G}} a\ d\sigma_f`.
That is, $`\sigma_f` has density $`\widehat{f}` with respect to the dual Haar
measure.
:::

:::proof "density_identity"
The symmetric identity
$`\int a\,\widehat{f}\ d\sigma_e = \int a\,\widehat{e}\ d\sigma_f` (from
density-form uniqueness and the inverse-transform bridge, both consequences of
{uses "fs_uniqueness" (intent := "auxiliary")}[] techniques and
{uses "finite_measure_fubini"}[]) is divided by $`\widehat{e}` on the support of
$`a` using an admissible square from {uses "exists_admissible_square"}[]; the
left side then computes against {uses "dual_haar"}[], the right side against
$`\sigma_f` from {uses "bochner"}[].
:::

:::theorem "fourier_inversion" (parent := "inversion") (lean := "IsPositiveType.fourier_inversion")
**Fourier inversion.** For $`f` continuous, integrable, of positive type:
$`\widehat{f}` is nonnegative, integrable against the dual Haar measure, and
$`f(x) = \int_{\hat{G}} \chi(x)\, \widehat{f}(\chi)\ d(\mathrm{dualHaar}\ \mu)(\chi)`
for every $`x \in G`. In particular
$`\int_{\hat{G}} \widehat{f}\ d(\mathrm{dualHaar}\ \mu) = f(1)`.
:::

:::proof "fourier_inversion"
By {uses "density_identity"}[] extended to bounded continuous integrands, the
integral of $`\chi(x)\,\widehat{f}(\chi)` against the dual Haar measure equals
$`\int \chi(x)\ d\sigma_f = f(x)` by {uses "bochner"}[]. Integrability of
$`\widehat{f}` needs a cutoff argument
(`exists_cutoff_integral_ge`) since dominated convergence along the
neighborhood net is unavailable.
:::

:::theorem "positive_type_bump" (parent := "inversion") (lean := "MeasureTheory.exists_positiveType_cc_eq_one")
**Positive-type bumps.** For every neighborhood $`U` of $`1` in $`G` there is a
continuous compactly supported function $`f` of positive type with
$`\operatorname{tsupport} f \subseteq U` and $`f(1) = 1`. These are the test
functions for both injectivity and the inducing property of the double-dual
evaluation.
:::

:::proof "positive_type_bump"
Choose a normalized bump $`h` ({uses "normalized_bump"}[]) supported in a small
$`V` with $`V \cdot V^{-1} \subseteq U` and normalize the convolution square
$`h \star h^*`, which is of positive type by
{uses "conv_square_positive_type"}[].
:::

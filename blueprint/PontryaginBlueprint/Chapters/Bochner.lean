import Verso
import VersoManual
import VersoBlueprint
import Pontryagin.PositiveType
import Pontryagin.Bochner

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Positive-type functions and Bochner's theorem" =>

Bochner's theorem — every continuous positive-type function is the
Fourier–Stieltjes transform of a unique finite positive regular measure on
$`\hat{G}` — is proved here by the positive-functional/Gelfand route
(Naimark/Loomis): no GNS construction, no spectral theorem, no Krein–Milman, and
no extreme-point analysis of the positive-type cone are needed.

:::group "bochner"
Functions of positive type, the induced positive functional on $`L^1(G)`, the
spectral bound, and Bochner's theorem via Riesz–Markov.
:::

:::definition "positive_type" (parent := "bochner") (lean := "IsPositiveType")
**Positive type.** A function $`f \colon G \to \mathbb{C}` is of *positive type*
if all finite matrices $`\big(f(x_i^{-1} x_j)\big)_{ij}` are positive
semidefinite:
$`0 \le \sum_{i,j} \overline{c_i}\, c_j\, f(x_i^{-1} x_j)`
for all $`x \colon \mathrm{Fin}\ n \to G` and
$`c \colon \mathrm{Fin}\ n \to \mathbb{C}`.
:::

:::theorem "positive_type_bound" (parent := "bochner") (lean := "IsPositiveType.norm_apply_le")
Elementary consequences of {uses "positive_type"}[]: $`0 \le f(1)`, hermitian
symmetry $`f(x^{-1}) = \overline{f(x)}`, and the bound
$`\lVert f(x) \rVert \le \mathrm{Re}\, f(1)` for every $`x`.
:::

:::proof "positive_type_bound"
Apply the defining inequality to the two-point families $`(1, x)` with suitable
coefficients: the $`2 \times 2` positive-semidefiniteness gives the hermitian
symmetry and the determinant condition gives the bound.
:::

:::theorem "char_positive_type" (parent := "bochner") (lean := "isPositiveType_char")
Every continuous character $`\chi \in \hat{G}` is of positive type; more
generally so is $`x \mapsto \int_{\hat{G}} \chi(x)\, d\sigma(\chi)` for any
finite measure $`\sigma` on the dual — the easy half of Bochner's theorem.
:::

:::proof "char_positive_type"
The double sum for a character factors as
$`\big| \sum_i c_i\, \chi(x_i) \big|^2 \ge 0` ({uses "positive_type"}[]);
integrating pointwise nonnegative sums preserves nonnegativity.
:::

:::theorem "conv_square_positive_type" (parent := "bochner") (lean := "isPositiveType_mconv_mstar")
**Convolution squares are of positive type:** for continuous compactly supported
$`g` (or $`g \in L^2(\mu)`), the function $`g \star g^*` is of positive type,
where $`\star` and the involution are those of {uses "mconv_def"}[].
:::

:::proof "conv_square_positive_type"
The double sum against $`g \star g^*` rewrites, by translation invariance of
$`\mu`, as $`\int \big| \sum_i c_i\, g(x_i^{-1} y) \big|^2 d\mu(y) \ge 0`
({uses "positive_type"}[]).
:::

:::theorem "positive_type_integral" (parent := "bochner") (lean := "IsPositiveType.integral_mconv_mstar_mul_nonneg")
**From finite sums to integrals.** For $`\varphi` continuous of positive type and
$`f` continuous compactly supported,
$`0 \le \int_G (f^* \star f)(x)\, \varphi(x)\, d\mu(x)`.
This is the bridge that turns the pointwise cone condition into positivity of a
functional on the convolution algebra.
:::

:::proof "positive_type_integral"
A Riemann-sum approximation: the compactly supported kernel is approximated
uniformly by its values on a finite Borel partition of the support subordinate to
translates of a small neighborhood of $`1`; each Riemann sum is nonnegative by
{uses "positive_type"}[], and the iterated-integral bookkeeping goes through
{uses "cc_fubini"}[]. No product measures are used.
:::

:::definition "pos_pairing" (parent := "bochner") (lean := "MeasureTheory.posPairing")
**The positive functional.** For $`\varphi` continuous, bounded, of positive
type, `posPairing μ hφ hφc` is the continuous linear functional
$`T(F) = \int_G F(x)\, \varphi(x)\, d\mu(x)` on $`L^1(\mu)`, with
$`\lVert T(F) \rVert \le \mathrm{Re}\,\varphi(1) \cdot \lVert F \rVert_1`
(by {uses "positive_type_bound"}[]), conjugate-symmetric under the star
involution, and nonnegative on star-squares by
{uses "positive_type_integral"}[].
:::

:::theorem "pairing_fourier_bound" (parent := "bochner") (lean := "MeasureTheory.norm_posPairing_le_fourier")
**The fundamental spectral bound.** For every $`F \in L^1(\mu)`,
$`\lVert T(F) \rVert \le \mathrm{Re}\,\varphi(1) \cdot \lVert \widehat{F} \rVert_\infty`.
The functional {uses "pos_pairing"}[] is thus continuous for the sup-norm of the
Fourier transform, not merely for the $`L^1` norm.
:::

:::proof "pairing_fourier_bound"
Cauchy–Schwarz for the sesquilinear form $`B(X,Y) = T(X^\ast Y)` gives
$`\lVert T(F) \rVert^2 \le \mathrm{Re}\,\varphi(1) \cdot \mathrm{Re}\, T(F^\ast F)`
after an approximate-identity upgrade ({uses "approx_identity"}[]). Iterating
along the powers $`P^{2^n}` of $`P = F^\ast F` and invoking the spectral radius
formula {uses "gelfand_bound"}[] sends the correction terms to
$`\lVert \widehat{F} \rVert_\infty`.
:::

:::definition "bochner_functional" (parent := "bochner") (lean := "MeasureTheory.bochnerCLM")
**Transport to $`C_0(\hat{G})`.** By {uses "pairing_fourier_bound"}[] the
functional {uses "pos_pairing"}[] descends along the Fourier transform to a
well-defined continuous linear functional `bochnerCLM` on the dense subalgebra of
transforms, and extends to all of $`C_0(\hat{G}, \mathbb{C})` by
{uses "fourier_dense"}[]. It is star-compatible and positive (by a square-root
approximation trick).
:::

:::theorem "bochner" (parent := "bochner") (lean := "IsPositiveType.exists_bochner_measure")
**Bochner's theorem (existence).** Every continuous function
$`\varphi \colon G \to \mathbb{C}` of positive type is the Fourier–Stieltjes
transform of a finite positive regular measure $`\sigma` on $`\hat{G}`:
$`\varphi(x) = \int_{\hat{G}} \chi(x)\, d\sigma(\chi)` for all $`x \in G`,
with total mass $`\sigma(\hat{G}) = \mathrm{Re}\,\varphi(1)`.
:::

:::proof "bochner"
Riesz–Markov–Kakutani (Mathlib's `RealRMK.rieszMeasure`) represents the positive
functional {uses "bochner_functional"}[] restricted to $`C_c(\hat{G})` by a
regular measure $`\sigma_0`, which is finite with mass at most
$`\mathrm{Re}\,\varphi(1)`. Testing against $`C_c` functions and the Fubini
identity `integral_fourierTransform_cc` ({uses "finite_measure_fubini"}[])
identify $`\varphi` with the character integral of $`\sigma_0` pushed forward by
inversion of the dual group; the $`L^1` identification uses
{uses "l1_testing"}[].
:::

:::theorem "bochner_unique" (parent := "bochner") (lean := "IsPositiveType.bochner_measure_unique")
**Bochner's theorem (uniqueness).** The representing measure of
{uses "bochner"}[] is unique: two finite positive regular measures on $`\hat{G}`
with the same character integrals $`x \mapsto \int \chi(x)\, d\sigma` are equal.
:::

:::proof "bochner_unique"
Immediate from Fourier–Stieltjes uniqueness, {uses "fs_uniqueness"}[].
:::

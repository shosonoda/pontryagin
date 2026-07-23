import Verso
import VersoManual
import VersoBlueprint
import Pontryagin.Plancherel

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Plancherel theory" =>

With the dual Haar measure in hand, the Fourier transform becomes an isometry
$`L^2(G) \to L^2(\hat{G})` — surjectively. The surjectivity is what ultimately
produces, for every nonempty open subset of $`\hat{G}`, an integrable function
whose transform lives exactly there: the *localized transforms* that drive the
surjectivity of Pontryagin duality itself.

:::group "plancherel"
The Parseval identity, the Plancherel isometry $`L^2(G) \cong L^2(\hat{G})`, its
surjectivity, and localized Fourier transforms.
:::

:::theorem "cc_close_l1_l2" (parent := "plancherel") (lean := "MeasureTheory.exists_cc_close_L1_L2")
**Simultaneous approximation.** A function in $`L^1 \cap L^2` can be approximated
by a single continuous compactly supported function simultaneously in the $`L^1`
and $`L^2` norms.
:::

:::proof "cc_close_l1_l2"
Truncate in range, approximate in $`L^1` by {uses "cc_dense_L1"}[], and clamp the
approximant back into the ball of bounded functions — clamping only improves both
norms. Uses the $`L^p` density machinery of {uses "cc_dense_Lp"}[].
:::

:::theorem "mconv_mul_consistency" (parent := "plancherel") (lean := "MeasureTheory.mconv_ae_eq_mulCLM")
**Pointwise/abstract consistency.** For $`f, g \in L^1 \cap L^2`, the pointwise
convolution `mconv μ f g` (everywhere defined by Cauchy–Schwarz) is an
almost-everywhere representative of the abstract $`L^1`-algebra product
{uses "l1_mul"}[] of the classes of $`f` and $`g`.
:::

:::proof "mconv_mul_consistency"
Approximate both factors simultaneously in $`(L^1, L^2)` by
{uses "cc_close_l1_l2"}[]; on $`C_c` the two products agree by definition of
{uses "l1_mul"}[], the abstract side converges in $`L^1`, and the pointwise side
converges uniformly by the $`L^2 \times L^2` Cauchy–Schwarz bound of
{uses "mconv_def"}[].
:::

:::theorem "parseval" (parent := "plancherel") (lean := "MeasureTheory.integral_norm_sq_fourierTransform")
**Parseval/Plancherel identity.** For $`f \in L^1 \cap L^2`:
$`\int_{\hat{G}} \lVert \widehat{f} \rVert^2\ d(\mathrm{dualHaar}\ \mu)
= \int_G \lVert f \rVert^2\ d\mu`,
and $`\widehat{f} \in L^2(\mathrm{dualHaar}\ \mu)`.
:::

:::proof "parseval"
For continuous compactly supported $`v`, apply Fourier inversion
({uses "fourier_inversion"}[]) to the positive-type convolution square
$`v \star v^*` at $`1`, whose transform is $`\lvert \widehat{v} \rvert^2` and
whose value at $`1` is $`\int \lVert v \rVert^2 d\mu`
({uses "conv_square_positive_type" (intent := "auxiliary")}[]). Extend to
$`L^1 \cap L^2` by {uses "cc_close_l1_l2"}[].
:::

:::definition "plancherel_isometry" (parent := "plancherel") (lean := "MeasureTheory.plancherelLI")
**The Plancherel isometry.** `plancherelLI μ : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 (dualHaar μ)`
is the unique isometric extension of
$`v \mapsto \text{class of } \widehat{v}` from the dense subspace of $`C_c`
classes ({uses "cc_dense_Lp"}[]) — an isometry by {uses "parseval"}[]. It agrees
with the pointwise transform on all of $`L^1 \cap L^2`.
:::

:::theorem "dual_uniqueness" (parent := "plancherel") (lean := "MeasureTheory.ae_eq_zero_of_forall_integral_char_mul_eq_zero")
**Dual uniqueness (density form).** If $`w` is integrable on $`\hat{G}` against
the dual Haar measure and all its "inverse Fourier coefficients" vanish —
$`\int_{\hat{G}} \chi(x)\, w(\chi)\ d(\mathrm{dualHaar}\ \mu)(\chi) = 0` for
every $`x \in G` — then $`w = 0` almost everywhere.
:::

:::proof "dual_uniqueness"
Multiply $`w` by the transforms $`\widehat{e}` of admissible squares
({uses "exists_admissible_square"}[]), which are integrable densities of Bochner
measures by {uses "density_identity"}[]; the hypothesis and
{uses "fs_uniqueness"}[]-style testing force $`w \cdot \widehat{e} = 0` a.e. on
every compact, and the lower bound $`\widehat{e} \ge 1/4` lets $`e` be divided
out. Testing against $`C_c` uses {uses "l1_testing"}[].
:::

:::theorem "plancherel_surjective" (parent := "plancherel") (lean := "MeasureTheory.surjective_plancherelLI")
**Surjectivity of Plancherel.** The isometry {uses "plancherel_isometry"}[] is
surjective: the Fourier transform is a unitary equivalence
$`L^2(G) \cong L^2(\hat{G})`.
:::

:::proof "plancherel_surjective"
The range is a closed subspace (isometric image of a complete space). Any $`w`
orthogonal to the range has all inverse Fourier coefficients zero — orthogonality
against transforms of $`C_c` functions unwinds, via
{uses "cc_fubini" (intent := "technical")}[], to the hypothesis of
{uses "dual_uniqueness"}[] — hence vanishes.
:::

:::theorem "localized_transform" (parent := "plancherel") (lean := "MeasureTheory.exists_integrable_fourierTransform_eq_zero_compl")
**Localized transforms.** For every nonempty open $`\Omega \subseteq \hat{G}`
there is an integrable $`\Phi \colon G \to \mathbb{C}` whose Fourier transform is
not identically zero but vanishes outside $`\Omega`.
:::

:::proof "localized_transform"
Take indicator functions of small compact neighborhoods inside $`\Omega`, pull
them back through {uses "plancherel_surjective"}[], and let $`\Phi` be the
pointwise product of the two preimages: by polarization of {uses "parseval"}[],
$`\widehat{\Phi}` is computed *exactly* as the convolution of the two indicators
on the dual, which is supported in $`\Omega` and not identically zero.
:::

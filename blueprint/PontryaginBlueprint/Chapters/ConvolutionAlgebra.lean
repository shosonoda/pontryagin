import Verso
import VersoManual
import VersoBlueprint
import Pontryagin.Convolution
import Pontryagin.L1Algebra

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The L¹ convolution algebra" =>

Mathlib's Bochner convolution is additive-only, and transporting through
`Additive G` would poison every character statement, so convolution is defined
in-project, multiplicatively. All algebra laws are proved pointwise for continuous
compactly supported functions — where the Fubini theorem of the Foundations
chapter applies — and then extended to $`L^1(G)` by bilinear continuity along the
dense subspace of $`C_c` classes.

:::group "l1_algebra"
The convolution product and star involution on $`C_c(G)`, and their density
extension to the commutative non-unital Banach star-algebra $`L^1(G)`.
:::

:::definition "mconv_def" (parent := "l1_algebra") (lean := "MeasureTheory.mconv, MeasureTheory.mstar")
**Convolution and involution.** For $`f, g \colon G \to \mathbb{C}` the
(multiplicative) convolution and the star involution are
$`(f \star g)(x) = \int_G f(y)\, g(y^{-1} x)\, d\mu(y)`, written `mconv μ f g`,
and $`f^*(x) = \overline{f(x^{-1})}`, written `mstar f`. For continuous compactly
supported $`f, g` the convolution is again continuous and compactly supported.
:::

:::theorem "mconv_comm" (parent := "l1_algebra") (lean := "MeasureTheory.mconv_comm")
Convolution is commutative: $`f \star g = g \star f` for all
$`f, g \colon G \to \mathbb{C}` (pointwise, wherever the defining integrals make
sense — on $`C_c` functions in particular).
:::

:::proof "mconv_comm"
Substitute $`y \mapsto y^{-1} x` in the defining integral of
{uses "mconv_def"}[], using inverse- and translation-invariance of the Haar
measure on the abelian group $`G`.
:::

:::theorem "mconv_assoc" (parent := "l1_algebra") (lean := "MeasureTheory.mconv_assoc")
Convolution of continuous compactly supported functions is associative:
$`(f \star g) \star k = f \star (g \star k)`.
:::

:::proof "mconv_assoc"
Unfold both sides as iterated integrals of a jointly continuous compactly
supported kernel and swap the order of integration by {uses "cc_fubini"}[],
using {uses "mconv_def"}[] and translation invariance of $`\mu`.
:::

:::theorem "mconv_norm" (parent := "l1_algebra") (lean := "MeasureTheory.integral_norm_mconv_le")
**Submultiplicativity in the $`L^1` norm (Young's inequality for $`p = 1`).**
For continuous compactly supported $`f, g`:
$`\int_G \lVert (f \star g)(x) \rVert \, d\mu(x) \le
\left( \int_G \lVert f \rVert \, d\mu \right) \left( \int_G \lVert g \rVert \, d\mu \right)`.
:::

:::proof "mconv_norm"
Bound the norm of the inner integral of {uses "mconv_def"}[] by the integral of
norms, swap the two integrals by {uses "cc_fubini"}[], and evaluate the inner
translation integral by invariance of $`\mu`.
:::

:::theorem "dense_cc_submodule" (parent := "l1_algebra") (lean := "MeasureTheory.dense_ccSubmodule")
The subspace `ccSubmodule μ` of $`L^1(\mu)` consisting of classes with a
continuous compactly supported representative is dense.
:::

:::proof "dense_cc_submodule"
Immediate from the density of $`C_c` in $`L^1`, {uses "cc_dense_L1"}[].
:::

:::definition "l1_mul" (parent := "l1_algebra") (lean := "MeasureTheory.mulCLM")
**Convolution on $`L^1`.** The bilinear map
$`\mathrm{mulCLM}\ \mu \colon L^1(\mu) \to L^1(\mu) \to L^1(\mu)` is the unique
continuous bilinear extension of $`C_c` convolution along the dense inclusion of
{uses "dense_cc_submodule"}[]; its operator norm is at most $`1` by
{uses "mconv_norm"}[].
:::

:::definition "l1_algebra_def" (parent := "l1_algebra") (lean := "MeasureTheory.L1G")
**The Banach star-algebra $`L^1(G)`.** The type synonym `L1G μ` of
$`L^1(\mu)` carries the instances `NonUnitalNormedCommRing`, `NormedSpace ℂ`,
`StarRing`, `NormedStarGroup`, and `CompleteSpace`: multiplication is
{uses "l1_mul"}[], commutativity and associativity extend from
{uses "mconv_comm"}[] and {uses "mconv_assoc"}[] by density and continuity, and
the involution is the isometry induced by $`f^*(x) = \overline{f(x^{-1})}`.
:::

:::theorem "approx_identity" (parent := "l1_algebra") (lean := "MeasureTheory.L1G.exists_bump_mul_close")
**Approximate identity.** For every $`F \in L^1(G)` and $`\varepsilon > 0` there
is a neighborhood $`U` of $`1` such that every normalized bump $`h` supported in
$`U` satisfies $`\lVert h \star F - F \rVert_1 \le \varepsilon` in
{uses "l1_algebra_def"}[]; moreover $`\lVert h \rVert_1 = 1`.
:::

:::proof "approx_identity"
For continuous compactly supported $`F` this is an explicit
$`\varepsilon`-estimate from uniform continuity (`exists_bump_mconv_close`);
the general case follows by approximating $`F` with
{uses "dense_cc_submodule"}[] and using $`\lVert h \rVert_1 = 1` from
{uses "normalized_bump"}[]. Filter-based dominated convergence is unavailable —
the identity-neighborhood net is not countably generated — so everything is an
explicit estimate.
:::

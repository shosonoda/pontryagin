import Verso
import VersoManual
import VersoBlueprint
import Pontryagin.CcFubini
import Pontryagin.FiniteMeasureFubini
import Pontryagin.Density
import Pontryagin.DensityLp
import Pontryagin.StoneWeierstrassC0
import Pontryagin.Topology
import Pontryagin.Translation
import Pontryagin.DualPolars

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Foundations" =>

:::author "pontryagin_contributors" (name := "The pontryagin contributors")
:::

Throughout, $`G` is a locally compact Hausdorff abelian group, written
multiplicatively, with a regular Haar measure $`\mu`, and
$`\hat{G} = \mathrm{PontryaginDual}\ G` is its dual group of continuous characters
$`\chi \colon G \to \mathbb{T}`, carrying the compact-open topology. This chapter
collects the measure-theoretic and topological infrastructure on which the whole
proof rests. A deliberate design constraint runs through all of it: on a general
LCA group the Haar measure need not be s-finite and product σ-algebras can fail to
see jointly continuous kernels, so **no product measures appear anywhere** —
every iterated-integral manipulation is done for continuous compactly supported
functions first and extended by density.

# Fubini without product measures

:::group "foundations"
Measure-theoretic and topological infrastructure: Fubini for compactly supported
kernels, density of $`C_c` in $`L^p`, Stone–Weierstrass for $`C_0`, normalized
bumps, translation operators, and the polar description of the dual topology.
:::

:::theorem "cc_fubini" (parent := "foundations") (lean := "integral_integral_swap_of_continuous_compactSupport")
**Fubini for jointly continuous compactly supported kernels.** For a jointly
continuous, compactly supported kernel $`F \colon X \times Y \to E` on topological
spaces carrying Borel-compatible measures that are finite on compacts, the two
iterated Bochner integrals agree:
$`\int_X \int_Y F(x,y)\,d\nu\,d\mu = \int_Y \int_X F(x,y)\,d\mu\,d\nu`.
No product measure, s-finiteness, regularity, or second-countability hypotheses
are needed; this is the measure-theoretic workhorse of the entire project.
:::

:::proof "cc_fubini"
Compact support forces separable range, which yields product measurability of the
kernel; the swap then follows from Mathlib's
`integral_integral_swap_of_hasCompactSupport`. The file packages it with the slice
lemmas (continuity, compact support, and integrability of the partial integrals)
that make iterated integrals of such kernels usable downstream.
:::

:::theorem "finite_measure_fubini" (parent := "foundations") (lean := "integral_integral_swap_of_finite_of_compactSupport")
**Fubini against a finite measure.** The swap of {uses "cc_fubini"}[] extends to
bounded jointly continuous kernels compactly supported in only *one* variable,
integrated in the other variable against a finite inner regular measure
$`\sigma`. This is the form needed for the symmetric measure identity: there the
kernel $`(x, \chi) \mapsto f(x)\,\chi(x)\,g(\chi)` on $`G \times \hat{G}` is
compactly supported in $`x` only.
:::

:::proof "finite_measure_fubini"
Truncate the kernel by Urysohn cutoffs equal to $`1` on an increasing sequence of
compact sets exhausting $`\sigma` (inner regularity), apply the compactly
supported swap to each truncation, and pass to the limit on both sides by
dominated convergence.
:::

# Density of test functions

:::theorem "cc_dense_L1" (parent := "foundations") (lean := "exists_hasCompactSupport_integral_norm_sub_le")
**$`C_c` is dense in $`L^1`.** On a locally compact Hausdorff space with a regular
Borel measure, every integrable function is within $`\varepsilon` (in the $`L^1`
norm) of a continuous compactly supported function. Mathlib's version assumes
`NormalSpace`, which fails for general locally compact Hausdorff spaces; this is
reproved via the locally compact Urysohn lemma.
:::

:::proof "cc_dense_L1"
Reduce by `MemLp.induction_dense` to scaled indicators of finite-measure sets;
approximate those using regularity of the measure and the locally compact form of
Urysohn's lemma (`exists_continuous_one_zero_of_isCompact`).
:::

:::theorem "l1_testing" (parent := "foundations") (lean := "ae_eq_zero_of_forall_integral_mul_eq_zero")
**$`L^1` functions are determined by testing against $`C_c`.** If $`u` is
integrable and $`\int u\,\varphi\,d\mu = 0` for every continuous compactly
supported test function $`\varphi`, then $`u = 0` almost everywhere.
:::

:::proof "l1_testing"
Approximate $`u` in $`L^1` by a continuous compactly supported $`v` using
{uses "cc_dense_L1"}[], then test against
$`\varphi := \overline{v} / \max(\lVert v \rVert, \delta)` and let
$`\delta \to 0`. No $`L^1`–$`L^\infty` duality is used.
:::

:::theorem "cc_dense_Lp" (parent := "foundations") (lean := "dense_ccLp, dense_ccL2")
**$`C_c` is dense in $`L^p`** for every exponent $`p \neq \infty`: the set of
classes in $`L^p(\mu)` admitting a continuous compactly supported representative
is dense. The case $`p = 2` is what the Plancherel layer consumes.
:::

:::proof "cc_dense_Lp"
The proof mirrors {uses "cc_dense_L1"}[] step by step; the only $`p`-specific
ingredients, `exists_Lp_half` and `exists_eLpNorm_indicator_le`, are available in
Mathlib for arbitrary $`p \neq \infty`.
:::

:::theorem "stone_weierstrass_c0" (parent := "foundations") (lean := "ZeroAtInftyContinuousMap.nonUnitalStarSubalgebra_dense_of_separatesPoints")
**Stone–Weierstrass for $`C_0`.** A non-unital star subalgebra of
$`C_0(X, \mathbb{k})`, the continuous functions vanishing at infinity on a locally
compact Hausdorff space, is dense provided it separates the points of $`X` and
vanishes nowhere.
:::

:::proof "stone_weierstrass_c0"
Pass to the one-point compactification: functions vanishing at infinity extend by
$`0` to $`C(X^+, \mathbb{k})`, isometrically identifying $`C_0(X, \mathbb{k})`
with the kernel of evaluation at $`\infty`. The unital star subalgebra generated
by the image separates the points of $`X^+`, hence is dense by the compact
Stone–Weierstrass theorem; intersecting with the kernel of evaluation at $`\infty`
recovers density.
:::

# Topology of locally compact groups and their duals

:::lemma_ "locally_closed" (parent := "foundations") (lean := "IsLocallyClosed.of_locallyCompactSpace")
A locally compact subspace of a Hausdorff space is locally closed.
:::

:::theorem "subgroup_closed" (parent := "foundations") (lean := "Subgroup.isClosed_of_locallyCompactSpace")
A locally compact subgroup of a Hausdorff topological group is closed. This is
what upgrades the embedding of $`G` into its double dual to a *closed* embedding.
:::

:::proof "subgroup_closed"
By {uses "locally_closed"}[] the subgroup is locally closed, hence open in its
closure; an open subgroup of a topological group is closed, so the subgroup equals
its closure.
:::

:::theorem "normalized_bump" (parent := "foundations") (lean := "exists_normalized_bump")
**Normalized bumps.** For every neighborhood $`U` of $`1` in $`G` there is a
nonnegative continuous compactly supported real function $`h` with
$`\operatorname{tsupport} h \subseteq U` and $`\int h \, d\mu = 1`. These bumps
are the raw material for all approximate-identity arguments.
:::

:::proof "normalized_bump"
Take a Urysohn function equal to $`1` on a compact neighborhood of $`1` inside
$`U` and normalize; the integral is positive because Haar measure is positive on
open sets.
:::

:::definition "translate_lp" (parent := "foundations") (lean := "translateLp, mtranslate")
**Translation operators.** Left translation
$`(\tau_a f)(x) = f(a^{-1} x)` acts on functions (`mtranslate`) and descends to a
linear isometry $`\tau_a \colon L^p(\mu) \to L^p(\mu)` (`translateLp`) for each
$`a \in G`, satisfying $`\tau_1 = \mathrm{id}` and
$`\tau_a \circ \tau_b = \tau_{ab}`.
:::

:::theorem "continuous_translate" (parent := "foundations") (lean := "continuous_translateLp")
For $`p \neq \infty` and fixed $`f \in L^p(\mu)`, the map
$`a \mapsto \tau_a f` is continuous from $`G` to $`L^p(\mu)`; that is,
{uses "translate_lp"}[] is a strongly continuous isometric action.
:::

:::proof "continuous_translate"
Via Mathlib's `Lp.compMeasurePreserving` and `DomMulAct` translation continuity,
which need only inner regularity of the Haar measure — no σ-finiteness.
:::

# Polars and the dual topology

:::lemma_ "circle_power_control" (parent := "foundations") (lean := "Circle.abs_arg_le_div_of_pow_mem_centeredArc")
**Quantitative power control on the circle.** If $`z, z^2, \dots, z^m` all lie in
the closed quarter arc around $`1`, then
$`\lvert \arg z \rvert \le \pi / (4m)`. This "no small subgroups" estimate is what
turns the qualitative compact-open topology of $`\hat{G}` into quantitative
uniform bounds.
:::

:::theorem "compact_polar" (parent := "foundations") (lean := "PontryaginDual.isCompact_polar")
**Polars of neighborhoods are compact.** For a neighborhood $`U` of $`1` in
$`G`, the polar — the set of characters mapping $`U` into the closed quarter arc —
is compact in $`\hat{G}`. No local compactness of $`G` is needed.
:::

:::proof "compact_polar"
The power-control estimate {uses "circle_power_control"}[] makes the polar an
equicontinuous family; compactness follows from the Arzelà–Ascoli theorem for the
compact-open topology.
:::

:::theorem "dual_nhds_basis" (parent := "foundations") (lean := "PontryaginDual.hasBasis_nhds_one")
**Neighborhood basis of the dual.** The sets
$`\{\chi \mid \forall x \in K,\ \chi(x) \in \mathrm{arc}(r)\}`, for $`K \subseteq G`
compact and $`0 < r \le \pi`, form a neighborhood basis of $`1` in $`\hat{G}`.
This concrete description of the compact-open topology is used to verify that the
double-dual evaluation is inducing.
:::

:::proof "dual_nhds_basis"
Compact-open basic sets are refined by arc conditions using
{uses "circle_power_control" (intent := "technical")}[] and the chord–arc
comparison on the circle.
:::

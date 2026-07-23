import Verso
import VersoManual
import VersoBlueprint
import Pontryagin.EvalInjective
import Pontryagin.Duality
import Solution

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Pontryagin duality" =>

The analytic machinery now yields the three core facts about the evaluation map
$`\mathrm{eval} \colon G \to \hat{\hat{G}}`, $`\mathrm{eval}(g)(\chi) = \chi(g)`:
it is injective, inducing, and surjective. Assembling them gives the duality
theorem. Note that the whole analytic stack applies to $`\hat{G}` as well as
$`G` — surjectivity uses localized transforms *on the dual group* — which is why
every lemma of the preceding chapters is stated for a general LCA group with an
arbitrary regular Haar measure.

:::group "duality"
The three core properties of the double-dual evaluation map, and the assembly of
the final isomorphism.
:::

:::theorem "eval_injective" (parent := "duality") (lean := "PontryaginDual.eval_injective, PontryaginDual.eval_injective_aux")
**Characters separate points.** The evaluation map
$`\mathrm{eval} \colon G \to \hat{\hat{G}}` is injective: if $`\chi(z) = 1` for
every character $`\chi`, then $`z = 1`.
:::

:::proof "eval_injective"
If $`z \neq 1`, pick by {uses "positive_type_bump"}[] a continuous compactly
supported positive-type $`f` with $`\operatorname{tsupport} f \subseteq \{z\}^c`
and $`f(1) = 1`. Fourier inversion ({uses "fourier_inversion"}[]) represents
$`f` as an integral of characters against $`\widehat{f}\cdot\mathrm{dualHaar}`;
since every character takes the value $`1` at $`z`, this forces
$`f(z) = f(1) = 1 \neq 0`, contradicting the support constraint.
:::

:::theorem "eval_inducing" (parent := "duality") (lean := "PontryaginDual.isInducing_eval, PontryaginDual.isInducing_eval_aux")
**The evaluation map is inducing:** the topology of $`G` is recovered from
uniform convergence of characters on compact subsets of $`\hat{G}`.
:::

:::proof "eval_inducing"
Compare neighborhood filters at $`1`. Given $`U \in \mathcal{N}(1)`, take $`f`
of positive type supported in $`U` with $`f(1) = 1`
({uses "positive_type_bump"}[]). Its transform is nonnegative with total
dual-Haar integral $`1` ({uses "fourier_inversion"}[]), and all but $`1/4` of
this mass lives on a compact set $`Q` of characters. If $`\mathrm{eval}(x)` lies
in the basic double-dual neighborhood determined by $`Q`
({uses "dual_nhds_basis"}[]), inversion gives
$`\lVert f(x) - 1 \rVert \le 3/4`, so $`f(x) \neq 0` and
$`x \in \operatorname{tsupport} f \subseteq U`.
:::

:::theorem "closed_range" (parent := "duality") (lean := "PontryaginDual.isClosed_range_eval")
The image of the evaluation map is a **closed** subgroup of the double dual.
:::

:::proof "closed_range"
By {uses "eval_injective"}[] and {uses "eval_inducing"}[] the range is an
embedded copy of the locally compact group $`G`, hence a locally compact
subgroup of the Hausdorff group $`\hat{\hat{G}}`, and closed by
{uses "subgroup_closed"}[].
:::

:::theorem "eval_surjective" (parent := "duality") (lean := "PontryaginDual.eval_surjective")
**Every character of the dual group is an evaluation:** the map
$`\mathrm{eval} \colon G \to \hat{\hat{G}}` is surjective.
:::

:::proof "eval_surjective"
If the closed subgroup $`\mathrm{range}\ \mathrm{eval}`
({uses "closed_range"}[]) were proper, its complement would be a nonempty open
subset of $`\hat{\hat{G}}` carrying a localized transform
({uses "localized_transform"}[], applied to the LCA group $`\hat{G}` with its
dual Haar measure): a nonzero $`\Phi \in L^1(\hat{G})` whose transform vanishes
on $`\mathrm{range}\ \mathrm{eval}`. Vanishing at every evaluation character
means all inverse Fourier coefficients of $`\Phi` vanish, so $`\Phi = 0` a.e. by
{uses "dual_uniqueness"}[] — contradicting that its transform is somewhere
nonzero.
:::

:::definition "double_dual_iso" (parent := "duality") (lean := "PontryaginDual.toDoubleDual")
**The duality isomorphism.** `PontryaginDual.toDoubleDual G` is the evaluation
map bundled as an isomorphism of topological groups
$`G \simeq_{\mathrm{t}*} \hat{\hat{G}}`: bijective by {uses "eval_injective"}[]
and {uses "eval_surjective"}[], a homeomorphism onto by
{uses "eval_inducing"}[].
:::

:::theorem "pontryagin_duality" (parent := "duality") (lean := "pontryagin_duality")
**Pontryagin duality.** For every locally compact Hausdorff abelian topological
group $`G` there exists an isomorphism of topological groups
$`e \colon G \simeq \hat{\hat{G}}` with $`e(g)(\chi) = \chi(g)` for all $`g, \chi`.
This is the challenge statement, proved in `Solution.lean` with no `sorry` and
axioms exactly `propext`, `Classical.choice`, `Quot.sound`.
:::

:::proof "pontryagin_duality"
Immediate: {uses "double_dual_iso"}[] is such an isomorphism, and its action is
evaluation by definition.
:::

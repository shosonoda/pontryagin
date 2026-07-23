import Verso
import VersoManual
import VersoBlueprint
import Pontryagin.FourierTransform

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Fourier transform" =>

The Fourier transform sends an integrable function on $`G` to a bounded
continuous function on the dual group $`\hat{G}`. All identities proved here for
continuous compactly supported functions become the algebraic laws of the Gelfand
transform in the next chapter.

:::group "fourier"
The Fourier transform of integrable functions on $`G`, its symmetries, continuity,
and the Riemann–Lebesgue lemma.
:::

:::definition "fourier_def" (parent := "fourier") (lean := "PontryaginDual.fourierTransform")
**The Fourier transform.** For $`f \colon G \to \mathbb{C}` and a character
$`\chi \in \hat{G}`,
$`\widehat{f}(\chi) = \int_G f(x)\, \overline{\chi(x)}\, d\mu(x)`,
written `fourierTransform μ f χ`. For integrable $`f` it is bounded by
$`\lVert f \rVert_1`, and it intertwines translation with modulation, and the
involution of {uses "mconv_def" (intent := "auxiliary")}[] with complex
conjugation.
:::

:::theorem "fourier_mconv" (parent := "fourier") (lean := "PontryaginDual.fourierTransform_mconv")
**The transform is multiplicative on convolutions:** for continuous compactly
supported $`f, g`,
$`\widehat{f \star g} = \widehat{f} \cdot \widehat{g}`.
:::

:::proof "fourier_mconv"
Unfold {uses "fourier_def"}[] and {uses "mconv_def"}[], swap the two integrals by
{uses "cc_fubini"}[], and split the character
$`\overline{\chi(x)} = \overline{\chi(y)}\, \overline{\chi(y^{-1}x)}` before
translating the inner integral.
:::

:::theorem "fourier_continuous" (parent := "fourier") (lean := "PontryaginDual.continuous_fourierTransform")
The Fourier transform $`\widehat{f}` of an integrable function is continuous on
$`\hat{G}` (with its compact-open topology).
:::

:::proof "fourier_continuous"
Approximate $`f` in $`L^1` by $`C_c` functions ({uses "cc_dense_L1"}[]); for
compactly supported $`f` the transform is continuous by uniform smallness of
$`\lVert \chi - \chi_0 \rVert` on the support, using {uses "fourier_def"}[].
:::

:::theorem "riemann_lebesgue" (parent := "fourier") (lean := "PontryaginDual.tendsto_fourierTransform_cocompact")
**Riemann–Lebesgue lemma.** The Fourier transform of an integrable function
vanishes at infinity on the dual group: $`\widehat{f}(\chi) \to 0` along the
cocompact filter of $`\hat{G}`.
:::

:::proof "riemann_lebesgue"
The translation identity gives
$`\widehat{f}(\chi)\,(1 - \chi(a)) = \widehat{f - \tau_a f}(\chi)`; if
$`\widehat{f}(\chi)` is not small, then $`\chi` is trapped in the polar of a
neighborhood on which translation moves $`f` little
({uses "continuous_translate"}[]), and that polar is compact by
{uses "compact_polar"}[]. Uses {uses "fourier_def"}[].
:::

:::theorem "bump_fourier_close" (parent := "fourier") (lean := "PontryaginDual.exists_nhds_forall_bump_fourierTransform_close")
**Transforms of bumps are near $`1` on compacts.** For every compact
$`K \subseteq \hat{G}` and $`\varepsilon > 0` there is a neighborhood $`U` of
$`1` in $`G` such that every normalized bump $`h` supported in $`U` has
$`\lvert \widehat{h}(\chi) - 1 \rvert \le \varepsilon` for all $`\chi \in K`.
:::

:::proof "bump_fourier_close"
Characters in a compact set are uniformly close to $`1` on a small neighborhood
$`U` of the identity (`PontryaginDual.eventually_uniform_arc`); since a bump of
{uses "normalized_bump"}[] has $`\int h\,d\mu = 1` and support in $`U`, the
defining integral of {uses "fourier_def"}[] differs from $`1` by at most
$`\varepsilon`.
:::

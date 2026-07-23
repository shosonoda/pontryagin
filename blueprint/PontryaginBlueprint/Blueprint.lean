import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import PontryaginBlueprint.Chapters.Foundations
import PontryaginBlueprint.Chapters.ConvolutionAlgebra
import PontryaginBlueprint.Chapters.FourierTransform
import PontryaginBlueprint.Chapters.Spectrum
import PontryaginBlueprint.Chapters.Bochner
import PontryaginBlueprint.Chapters.Inversion
import PontryaginBlueprint.Chapters.Plancherel
import PontryaginBlueprint.Chapters.Duality

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Pontryagin Duality for Locally Compact Abelian Groups" =>

This blueprint documents a **complete** formalization, in Lean 4 / Mathlib, of
Pontryagin duality: for every locally compact Hausdorff abelian topological group
$`G`, the canonical evaluation map $`g \mapsto (\chi \mapsto \chi(g))` is an
isomorphism of topological groups onto the double Pontryagin dual
$`\hat{\hat{G}}`. The final theorem `pontryagin_duality` is proved with no
`sorry`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

The proof follows the classical analytic route — the $`L^1(G)` convolution
algebra, its Gelfand spectrum, Bochner's theorem via positive functionals, the
dual Haar measure, Fourier inversion, and Plancherel theory — with **no
σ-compactness or second-countability assumptions**, and, unusually, with **no
product measures anywhere**: every Fubini-type manipulation is performed on
continuous compactly supported kernels and extended to $`L^1` by density.

{include 0 PontryaginBlueprint.Chapters.Foundations}
{include 0 PontryaginBlueprint.Chapters.ConvolutionAlgebra}
{include 0 PontryaginBlueprint.Chapters.FourierTransform}
{include 0 PontryaginBlueprint.Chapters.Spectrum}
{include 0 PontryaginBlueprint.Chapters.Bochner}
{include 0 PontryaginBlueprint.Chapters.Inversion}
{include 0 PontryaginBlueprint.Chapters.Plancherel}
{include 0 PontryaginBlueprint.Chapters.Duality}

{blueprint_graph}
{blueprint_summary}

/-
Copyright (c) 2026 The pontryagin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The pontryagin contributors
-/
import Pontryagin.Basic
import Pontryagin.EvalInjective
import Pontryagin.Plancherel
import Pontryagin.Topology

/-!
# Pontryagin duality: assembly

The evaluation map `eval : G →ₜ* PontryaginDual (PontryaginDual G)` of a locally compact
Hausdorff abelian group is a topological group isomorphism.  This file assembles the final
equivalence `PontryaginDual.toDoubleDual` from three core facts, proved in the analytic
development:

* `eval_injective`: characters separate points;
* `isInducing_eval`: polars of compact sets of characters recover the topology of `G`;
* `eval_surjective`: every character of the dual group is an evaluation.

The intermediate step `isClosed_range_eval` (the image of `eval` is closed) is derived here
from `isInducing_eval` and the generic fact that a locally compact subgroup of a Hausdorff
group is closed.
-/

noncomputable section

open Function Topology

namespace PontryaginDual

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G]

/-- **Characters separate points**: the evaluation map into the double dual is injective. -/
theorem eval_injective : Injective (eval : G → PontryaginDual (PontryaginDual G)) :=
  eval_injective_aux G

/-- The evaluation map is inducing: the topology of `G` is recovered from uniform
convergence of characters on compact sets of the dual. -/
theorem isInducing_eval : IsInducing (eval : G → PontryaginDual (PontryaginDual G)) :=
  isInducing_eval_aux G

theorem isEmbedding_eval : IsEmbedding (eval : G → PontryaginDual (PontryaginDual G)) :=
  ⟨isInducing_eval G, eval_injective G⟩

/-- The image of the evaluation map is a closed subgroup of the double dual. -/
theorem isClosed_range_eval :
    IsClosed (Set.range (eval : G → PontryaginDual (PontryaginDual G))) := by
  -- the range as a subgroup, with carrier syntactically `Set.range eval`
  let H : Subgroup (PontryaginDual (PontryaginDual G)) :=
    ((eval (A := G)).toMonoidHom.range).copy
      (Set.range (eval : G → PontryaginDual (PontryaginDual G)))
      (by rw [MonoidHom.coe_range]; rfl)
  have : LocallyCompactSpace H :=
    ((isEmbedding_eval G).toHomeomorph).locallyCompactSpace_iff.mp inferInstance
  simpa [H, Subgroup.coe_copy] using Subgroup.isClosed_of_locallyCompactSpace H

set_option linter.style.show false in
/-- The evaluation map is surjective: every character of the dual group is an evaluation.

If the closed subgroup `range eval` were proper, its complement would be a nonempty open
set carrying a localized Fourier transform: a nonzero `Φ ∈ L¹` of the dual group whose
transform vanishes on `range eval`.  Vanishing at every evaluation character means the
inverse Fourier–Stieltjes transform of `Φ` vanishes identically, so `Φ = 0` a.e. by the
density form of Fourier–Stieltjes uniqueness — contradicting that its transform is
somewhere nonzero. -/
theorem eval_surjective : Surjective (eval : G → PontryaginDual (PontryaginDual G)) := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  letI : MeasurableSpace (PontryaginDual G) := borel (PontryaginDual G)
  haveI : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  letI : MeasurableSpace (PontryaginDual (PontryaginDual G)) :=
    borel (PontryaginDual (PontryaginDual G))
  haveI : BorelSpace (PontryaginDual (PontryaginDual G)) := ⟨rfl⟩
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  set μ : MeasureTheory.Measure G := MeasureTheory.Measure.haarMeasure K₀ with hμ
  intro ω
  by_contra hω
  have hω' : ω ∈ (Set.range (eval : G → PontryaginDual (PontryaginDual G)))ᶜ := by
    simpa [Set.mem_range] using hω
  -- a localized transform supported in the open complement of the range
  obtain ⟨Φ, hΦint, ⟨χ₀, hχ₀⟩, hsupp⟩ :=
    exists_integrable_fourierTransform_eq_zero_compl (dualHaar μ)
      (isClosed_range_eval G).isOpen_compl ⟨ω, hω'⟩
  -- its transform vanishes at every evaluation character
  have hchar : ∀ x : G, ∫ χ, (χ x : ℂ) * Φ χ ∂(dualHaar μ) = 0 := by
    intro x
    have hv : fourierTransform (dualHaar μ) Φ (eval x⁻¹) = 0 := by
      refine hsupp _ ?_
      simp only [Set.mem_compl_iff, not_not]
      exact Set.mem_range_self x⁻¹
    rw [← hv, fourierTransform_apply]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun χ => ?_)
    show (χ x : ℂ) * Φ χ = Φ χ * (starRingEnd ℂ) ((eval (A := G) x⁻¹) χ : ℂ)
    have h1 : (eval (A := G) x⁻¹) χ = (χ x)⁻¹ := by
      rw [eval_apply, map_inv]
    rw [h1, Circle.coe_inv_eq_conj, Complex.conj_conj, mul_comm]
  -- hence Φ vanishes a.e., contradicting nontriviality of its transform
  have hΦ0 : Φ =ᵐ[dualHaar μ] 0 :=
    ae_eq_zero_of_forall_integral_char_mul_eq_zero μ hΦint hchar
  refine hχ₀ ?_
  rw [fourierTransform_congr_ae hΦ0, fourierTransform_apply]
  simp

theorem eval_bijective : Bijective (eval : G → PontryaginDual (PontryaginDual G)) :=
  ⟨eval_injective G, eval_surjective G⟩

/-- **Pontryagin duality**: the canonical evaluation map identifies a locally compact
Hausdorff abelian group with its double dual, as a topological group. -/
def toDoubleDual : G ≃ₜ* PontryaginDual (PontryaginDual G) :=
  { MulEquiv.ofBijective (eval (A := G)).toMonoidHom (eval_bijective G) with
    continuous_toFun := (eval (A := G)).continuous
    continuous_invFun := by
      exact ((MulEquiv.ofBijective (eval (A := G)).toMonoidHom
        (eval_bijective G)).toEquiv.toHomeomorphOfIsInducing
          (isInducing_eval G)).symm.continuous }

@[simp]
theorem toDoubleDual_apply (g : G) (χ : PontryaginDual G) :
    toDoubleDual G g χ = χ g := rfl

end PontryaginDual

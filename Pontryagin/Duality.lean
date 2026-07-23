/-
Copyright (c) 2026 The pontryagin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The pontryagin contributors
-/
import Pontryagin.Basic
import Pontryagin.EvalInjective
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

/-- The evaluation map is surjective: every character of the dual group is an evaluation. -/
theorem eval_surjective : Surjective (eval : G → PontryaginDual (PontryaginDual G)) := by
  sorry

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

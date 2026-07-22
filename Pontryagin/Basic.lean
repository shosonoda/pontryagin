/-
Copyright (c) 2026 The pontryagin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The pontryagin contributors
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Pontryagin duality for finite abelian groups

For a finite discrete abelian topological group `A`, the canonical evaluation map

`A → PontryaginDual (PontryaginDual A)`,  `a ↦ (χ ↦ χ a)`

is an isomorphism of topological groups.
-/

noncomputable section

open Function Multiplicative

namespace PontryaginDual

variable {A : Type*} [CommGroup A] [TopologicalSpace A]

section LocallyCompact

variable [LocallyCompactSpace A]

/-- The canonical evaluation homomorphism from a locally compact abelian group to its double
Pontryagin dual. -/
def eval : A →ₜ* PontryaginDual (PontryaginDual A) where
  toFun a :=
    { toFun := fun χ ↦ χ a
      map_one' := rfl
      map_mul' := fun χ ψ ↦ rfl
      continuous_toFun := by
        change Continuous (fun χ : A →ₜ* Circle ↦ χ a)
        exact continuous_eval_const a }
  map_one' := PontryaginDual.ext fun χ ↦ OneHomClass.map_one χ
  map_mul' a b := PontryaginDual.ext fun χ ↦ MulHomClass.map_mul χ a b
  continuous_toFun := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    change Continuous (fun p : A × (A →ₜ* Circle) ↦ p.2 p.1)
    exact continuous_eval.comp continuous_swap

@[simp]
theorem eval_apply (a : A) (χ : PontryaginDual A) : eval a χ = χ a := rfl

/-- The inverse of the evaluation map, assuming the two substantive conclusions of Pontryagin
duality: that evaluation is bijective and open. -/
def evalInvOfBijectiveOfIsOpenMap
    (hbij : Function.Bijective (eval : A → PontryaginDual (PontryaginDual A)))
    (hopen : IsOpenMap (eval : A → PontryaginDual (PontryaginDual A))) :
    PontryaginDual (PontryaginDual A) →ₜ* A := by
  let e : A ≃* PontryaginDual (PontryaginDual A) :=
    MulEquiv.ofBijective eval.toMonoidHom hbij
  exact
    { e.symm.toMonoidHom with
      continuous_toFun := (Equiv.continuous_symm_iff e.toEquiv).2 (by
        change IsOpenMap (eval : A → PontryaginDual (PontryaginDual A))
        exact hopen) }

end LocallyCompact

section Finite

variable [DiscreteTopology A]

/-- Regard an additive character of `Additive A` as a continuous character of the
discrete group `A`. -/
private def ofAddChar (f : AddChar (Additive A) Circle) : PontryaginDual A where
  toFun a := f (.ofMul a)
  map_one' := f.map_zero_eq_one
  map_mul' a b := f.map_add_eq_mul (.ofMul a) (.ofMul b)
  continuous_toFun := continuous_of_discreteTopology

@[simp]
private lemma ofAddChar_apply (f : AddChar (Additive A) Circle) (a : A) :
    ofAddChar f a = f (.ofMul a) := rfl

/-- Continuous characters of a discrete group are the same as additive characters of its
additive counterpart. -/
private def equivAddChar : PontryaginDual A ≃ AddChar (Additive A) Circle where
  toFun f :=
    { toFun := fun a ↦ f a.toMul
      map_zero_eq_one' := OneHomClass.map_one f
      map_add_eq_mul' := fun a b ↦ MulHomClass.map_mul f a.toMul b.toMul }
  invFun := ofAddChar
  left_inv _ := PontryaginDual.ext fun _ ↦ rfl
  right_inv _ := AddChar.ext _ _ fun _ ↦ rfl

/-- A finite discrete abelian group and its Pontryagin dual have the same cardinality. -/
private lemma card_dual [Fintype A] :
    Fintype.card (PontryaginDual A) = Fintype.card A := by
  letI : Fintype (Additive A) := Fintype.ofEquiv A Additive.ofMul
  letI : Fintype (AddChar (Additive A) Circle) :=
    Fintype.ofEquiv (AddChar (Additive A) ℂ) AddChar.circleEquivComplex.symm.toEquiv
  calc
    Fintype.card (PontryaginDual A) = Fintype.card (AddChar (Additive A) Circle) :=
      Fintype.card_congr equivAddChar
    _ = Fintype.card (AddChar (Additive A) ℂ) :=
      Fintype.card_congr AddChar.circleEquivComplex.toEquiv
    _ = Fintype.card (Additive A) := AddChar.card_eq
    _ = Fintype.card A := Fintype.card_congr Additive.toMul

private theorem eval_injective [Finite A] :
    Function.Injective (eval : A → PontryaginDual (PontryaginDual A)) := by
  intro a b hab
  have hadd : Additive.ofMul a = Additive.ofMul b := by
    apply AddChar.doubleDualEmb_injective
    apply AddChar.ext _ _
    intro ψ
    let θ : AddChar (Additive A) Circle := AddChar.circleEquivComplex.symm ψ
    have hcircle : θ (.ofMul a) = θ (.ofMul b) := by
      have h := DFunLike.congr_fun hab (ofAddChar θ)
      simpa using h
    rw [← AddChar.circleEquivComplex.apply_symm_apply ψ]
    exact congrArg ((↑) : Circle → ℂ) hcircle
  exact Additive.ofMul.injective hadd

private theorem eval_bijective [Finite A] :
    Function.Bijective (eval : A → PontryaginDual (PontryaginDual A)) := by
  letI := Fintype.ofFinite A
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨eval_injective, ?_⟩
  rw [card_dual, card_dual]

/-- **Pontryagin duality for finite abelian groups.**

The canonical evaluation map identifies a finite discrete abelian group with its double
Pontryagin dual, as a topological group. -/
def dualityEquiv [Finite A] : A ≃ₜ* PontryaginDual (PontryaginDual A) :=
  (MulEquiv.ofBijective eval.toMonoidHom eval_bijective).toContinuousMulEquiv (by simp)

@[simp]
theorem dualityEquiv_apply [Finite A] (a : A) (χ : PontryaginDual A) :
    dualityEquiv a χ = χ a := rfl

end Finite

end PontryaginDual

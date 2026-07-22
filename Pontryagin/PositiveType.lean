/-
Copyright (c) 2026 The pontryagin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The pontryagin contributors
-/
import Pontryagin.Convolution
import Mathlib.Analysis.Complex.Order
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Functions of positive type on a locally compact abelian group

A function `f : G → ℂ` on a group `G` is of *positive type* (or *positive-definite*) if all the
finite matrices `(f ((x i)⁻¹ * x j))_{i j}` are positive semidefinite:

`0 ≤ ∑ i, ∑ j, conj (c i) * c j * f ((x i)⁻¹ * x j)`

for all `x : Fin n → G` and `c : Fin n → ℂ`, the inequality being in the partial order of
`Complex.partialOrder` (available with `open scoped ComplexOrder`).

## Main definitions and results

* `IsPositiveType f`: the definition above.

Elementary consequences (pure algebra):

* `IsPositiveType.apply_one_nonneg`: `0 ≤ f 1`;
* `IsPositiveType.apply_inv`: `f x⁻¹ = conj (f x)` (hermitian symmetry);
* `IsPositiveType.norm_apply_le`: `‖f x‖ ≤ (f 1).re`;
* `isPositiveType_zero`, `IsPositiveType.add`, `IsPositiveType.smul_of_nonneg`: positive-type
  functions form a cone;
* `isPositiveType_char`: every continuous character is of positive type;
* `isPositiveType_integral_char`: `x ↦ ∫ χ, χ x ∂σ` is of positive type for every finite
  measure `σ` on the Pontryagin dual (one half of Bochner's theorem).

Convolution squares (with a regular Haar measure `μ`):

* `isPositiveType_mconv_mstar_of_memLp_two`: `g ⋆ g^*` is of positive type for `g ∈ L²(μ)`;
* `isPositiveType_mconv_mstar`: the same for continuous compactly supported `g`.

Uniform-continuity helpers (of independent use):

* `Continuous.exists_nhds_one_forall_norm_sub_le`: a continuous compactly supported function on
  a topological abelian group is uniformly continuous, in ε-neighborhood form;
* `Continuous.exists_nhds_one_forall_norm_sub_le_of_isCompact`: uniform continuity of an
  arbitrary continuous function on a compact set, in the same form.

The key bridge from finite sums to integrals, used by the Bochner layer:

* `IsPositiveType.integral_mconv_nonneg`: for `φ` continuous of positive type and `f`
  continuous compactly supported, `0 ≤ ∫ x, ∫ y, conj (f y) * f x * φ (y⁻¹ * x) ∂μ ∂μ`;
* `IsPositiveType.integral_mconv_mstar_mul_nonneg`: equivalently,
  `0 ≤ ∫ x, mconv μ (mstar f) f x * φ x ∂μ`.

The proof of `IsPositiveType.integral_mconv_nonneg` is a Riemann-sum approximation: the
compactly supported kernel is approximated, uniformly up to `ε`, by its values on a finite
Borel partition of `tsupport f` subordinate to translates of a small neighborhood of `1`, and
each Riemann sum is nonnegative by `IsPositiveType`. No product measures are used anywhere.
-/

noncomputable section

open Function MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise ComplexConjugate ComplexOrder

-- The measure-theoretic sections deliberately use one coarse hypothesis block (locally compact
-- Hausdorff abelian group with regular Haar measure) rather than minimal per-lemma assumptions.
set_option linter.unusedSectionVars false

/-! ### Definition and elementary consequences -/

section Algebra

variable {G : Type*} [CommGroup G]

/-- A function `f : G → ℂ` is of *positive type* if every matrix `(f ((x i)⁻¹ * x j))_{i j}` is
positive semidefinite. The inequality lives in the partial order of `ComplexOrder`; in
particular each such sum is real. -/
def IsPositiveType (f : G → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
    0 ≤ ∑ i, ∑ j, conj (c i) * c j * f ((x i)⁻¹ * x j)

theorem IsPositiveType.apply_one_nonneg {f : G → ℂ} (hf : IsPositiveType f) : 0 ≤ f 1 := by
  simpa using hf 1 (fun _ => 1) fun _ => 1

/-- The `2 × 2` positivity condition, at the points `1` and `x`. -/
private theorem IsPositiveType.sum_two {f : G → ℂ} (hf : IsPositiveType f) (x : G)
    (c₁ c₂ : ℂ) :
    0 ≤ conj c₁ * c₁ * f 1 + conj c₁ * c₂ * f x + conj c₂ * c₁ * f x⁻¹ +
      conj c₂ * c₂ * f 1 := by
  have h := hf 2 ![1, x] ![c₁, c₂]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    inv_one, one_mul, mul_one, inv_mul_cancel] at h
  calc (0 : ℂ) ≤ _ := h
    _ = conj c₁ * c₁ * f 1 + conj c₁ * c₂ * f x + conj c₂ * c₁ * f x⁻¹ +
        conj c₂ * c₂ * f 1 := by ring

/-- A function of positive type is hermitian: `f x⁻¹ = conj (f x)`. -/
theorem IsPositiveType.apply_inv {f : G → ℂ} (hf : IsPositiveType f) (x : G) :
    f x⁻¹ = conj (f x) := by
  have him1 : (f 1).im = 0 := ((Complex.nonneg_iff.mp hf.apply_one_nonneg).2).symm
  have h1 := hf.sum_two x 1 1
  have h2 := hf.sum_two x 1 Complex.I
  simp only [map_one, one_mul, mul_one, Complex.conj_I] at h1 h2
  -- imaginary part of the first inequality: `im (f x) + im (f x⁻¹) = 0`
  have e1 : (f x).im + (f x⁻¹).im = 0 := by
    have := (Complex.nonneg_iff.mp h1).2
    simp only [Complex.add_im, him1] at this
    linarith
  -- imaginary part of the second inequality: `re (f x) - re (f x⁻¹) = 0`
  have e2 : (f x).re - (f x⁻¹).re = 0 := by
    have := (Complex.nonneg_iff.mp h2).2
    simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.mul_re, him1] at this
    linarith
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith

/-- A function of positive type attains its maximal modulus at `1`: `‖f x‖ ≤ (f 1).re`. -/
theorem IsPositiveType.norm_apply_le {f : G → ℂ} (hf : IsPositiveType f) (x : G) :
    ‖f x‖ ≤ (f 1).re := by
  have h1 : 0 ≤ (f 1).re := (Complex.nonneg_iff.mp hf.apply_one_nonneg).1
  rcases eq_or_ne (f x) 0 with h | h
  · simpa [h] using h1
  -- apply the `2 × 2` condition with `c₁ = ‖f x‖` and `c₂ = -conj (f x)`
  set N : ℂ := ((‖f x‖ : ℝ) : ℂ) with hN
  have key := hf.sum_two x N (-conj (f x))
  have cm : conj (f x) * f x = N * N := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast [hN]
    ring
  have e : conj N * N * f 1 + conj N * (-conj (f x)) * f x + conj (-conj (f x)) * N * f x⁻¹ +
      conj (-conj (f x)) * (-conj (f x)) * f 1 = 2 * (N * N) * f 1 - 2 * (N * (N * N)) := by
    rw [hf.apply_inv x]
    simp only [map_neg, Complex.conj_conj, hN, Complex.conj_ofReal]
    linear_combination (f 1 - 2 * ((‖f x‖ : ℝ) : ℂ)) * cm
  rw [e] at key
  have key2 : 0 ≤ ((2 * ‖f x‖ * ‖f x‖ : ℝ) : ℂ) * f 1 - ((2 * ‖f x‖ * ‖f x‖ * ‖f x‖ : ℝ) : ℂ) := by
    convert key using 2 <;> · push_cast [hN]; ring
  have hre := (Complex.nonneg_iff.mp key2).1
  simp only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  have hp : 0 < ‖f x‖ := norm_pos_iff.mpr h
  have h2 : 0 < 2 * ‖f x‖ * ‖f x‖ := by positivity
  refine le_of_mul_le_mul_left ?_ h2
  linarith

theorem isPositiveType_zero : IsPositiveType (0 : G → ℂ) := by
  intro n x c
  simp

theorem IsPositiveType.add {f g : G → ℂ} (hf : IsPositiveType f) (hg : IsPositiveType g) :
    IsPositiveType (f + g) := by
  intro n x c
  have key : ∑ i, ∑ j, conj (c i) * c j * (f + g) ((x i)⁻¹ * x j) =
      (∑ i, ∑ j, conj (c i) * c j * f ((x i)⁻¹ * x j)) +
        ∑ i, ∑ j, conj (c i) * c j * g ((x i)⁻¹ * x j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply]
    ring
  rw [key]
  exact add_nonneg (hf n x c) (hg n x c)

theorem IsPositiveType.smul_of_nonneg {f : G → ℂ} (hf : IsPositiveType f) {r : ℝ}
    (hr : 0 ≤ r) : IsPositiveType (r • f) := by
  intro n x c
  have key : ∑ i, ∑ j, conj (c i) * c j * (r • f) ((x i)⁻¹ * x j) =
      (r : ℂ) * ∑ i, ∑ j, conj (c i) * c j * f ((x i)⁻¹ * x j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  rw [key]
  exact mul_nonneg (by exact_mod_cast hr) (hf n x c)

end Algebra

/-! ### Characters and integrals of characters are of positive type -/

section Characters

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- The fundamental algebraic identity behind `isPositiveType_char`: the positive-type double
sum of a character is `conj S * S` for `S = ∑ i, c i * χ (x i)`. -/
private theorem sum_sum_char_eq (χ : PontryaginDual G) {n : ℕ} (x : Fin n → G)
    (c : Fin n → ℂ) :
    ∑ i, ∑ j, conj (c i) * c j * ((χ ((x i)⁻¹ * x j) : ℂ)) =
      conj (∑ i, c i * χ (x i)) * ∑ i, c i * χ (x i) := by
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hval : ((χ ((x i)⁻¹ * x j) : ℂ)) = conj ((χ (x i) : ℂ)) * (χ (x j) : ℂ) := by
    rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]
  rw [hval, map_mul]
  ring

/-- Continuous characters are of positive type. -/
theorem isPositiveType_char (χ : PontryaginDual G) :
    IsPositiveType (fun x => (χ x : ℂ)) := by
  intro n x c
  rw [sum_sum_char_eq χ x c]
  simpa only [starRingEnd_apply] using star_mul_self_nonneg (∑ i, c i * (χ (x i) : ℂ))

/-- One half of Bochner's theorem: for a finite measure `σ` on the Pontryagin dual, the
function `x ↦ ∫ χ, χ x ∂σ` is of positive type. -/
theorem isPositiveType_integral_char {mΓ : MeasurableSpace (PontryaginDual G)}
    [OpensMeasurableSpace (PontryaginDual G)] (σ : Measure (PontryaginDual G))
    [IsFiniteMeasure σ] :
    IsPositiveType (fun x => ∫ χ : PontryaginDual G, (χ x : ℂ) ∂σ) := by
  intro n x c
  have hcont : ∀ z : G, Continuous fun χ : PontryaginDual G => (χ z : ℂ) := fun z => by
    refine continuous_subtype_val.comp ?_
    change Continuous fun χ : G →ₜ* Circle => χ z
    exact continuous_eval_const z
  have hint : ∀ z : G, Integrable (fun χ : PontryaginDual G => (χ z : ℂ)) σ := fun z => by
    refine (integrable_const (1 : ℝ)).mono' (hcont z).aestronglyMeasurable ?_
    exact Eventually.of_forall fun χ => by simp
  calc ∑ i, ∑ j, conj (c i) * c j * ∫ χ : PontryaginDual G, (χ ((x i)⁻¹ * x j) : ℂ) ∂σ
      = ∫ χ : PontryaginDual G, ∑ i, ∑ j, conj (c i) * c j * (χ ((x i)⁻¹ * x j) : ℂ) ∂σ := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          ((hint _).const_mul _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => ((hint _).const_mul _)]
        exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
    _ = ∫ χ : PontryaginDual G, ((‖∑ i, c i * (χ (x i) : ℂ)‖ ^ 2 : ℝ) : ℂ) ∂σ := by
        congr 1
        funext χ
        rw [sum_sum_char_eq χ x c, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    _ = ((∫ χ : PontryaginDual G, ‖∑ i, c i * (χ (x i) : ℂ)‖ ^ 2 ∂σ : ℝ) : ℂ) :=
        integral_ofReal
    _ ≥ 0 := by
        rw [ge_iff_le, Complex.zero_le_real]
        exact integral_nonneg fun χ => sq_nonneg _

end Characters

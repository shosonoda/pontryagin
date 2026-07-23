/-
Copyright (c) 2026 The pontryagin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The pontryagin contributors
-/
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Locally compact subspaces and subgroups

This file fills a gap in Mathlib (general-purpose material with no project-specific content)
and is a candidate for upstreaming; see `UPSTREAMING.md` for the audit and target locations.

Two generic facts used in the proof of Pontryagin duality:

* `IsLocallyClosed.of_locallyCompactSpace`: a locally compact subspace of a Hausdorff space
  is locally closed;
* `Subgroup.isClosed_of_locallyCompactSpace`: a locally compact subgroup of a Hausdorff
  topological group is closed.
-/

open scoped Pointwise

open Set Topology

variable {Y : Type*} [TopologicalSpace Y]

/-- A locally compact subspace of a Hausdorff space is locally closed. -/
theorem IsLocallyClosed.of_locallyCompactSpace [T2Space Y] (s : Set Y)
    [LocallyCompactSpace s] : IsLocallyClosed s := by
  have key : ∀ x ∈ s, ∃ U : Set Y, IsOpen U ∧ x ∈ U ∧ U ∩ closure s ⊆ s := by
    intro x hx
    obtain ⟨K, hK_mem, -, hK_comp⟩ :=
      local_compact_nhds (x := (⟨x, hx⟩ : s)) (n := univ) Filter.univ_mem
    rw [nhds_subtype_eq_comap, Filter.mem_comap] at hK_mem
    obtain ⟨t, ht_mem, ht_sub⟩ := hK_mem
    refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht_mem, ?_⟩
    have hC_comp : IsCompact (Subtype.val '' K) := hK_comp.image continuous_subtype_val
    have hC_sub : Subtype.val '' K ⊆ s := by
      rintro - ⟨k, -, rfl⟩
      exact k.2
    have h1 : interior t ∩ s ⊆ Subtype.val '' K := by
      rintro y ⟨hyU, hys⟩
      exact ⟨⟨y, hys⟩, ht_sub (mem_preimage.mpr (interior_subset hyU)), rfl⟩
    calc interior t ∩ closure s
        ⊆ closure (interior t ∩ s) := isOpen_interior.inter_closure
      _ ⊆ closure (Subtype.val '' K) := closure_mono h1
      _ = Subtype.val '' K := hC_comp.isClosed.closure_eq
      _ ⊆ s := hC_sub
  choose! U hUopen hxU hUsub using key
  refine ⟨⋃ x ∈ s, U x, closure s, isOpen_biUnion hUopen, isClosed_closure, ?_⟩
  apply subset_antisymm
  · exact fun y hy => ⟨mem_biUnion hy (hxU y hy), subset_closure hy⟩
  · rintro y ⟨hyU, hyc⟩
    obtain ⟨x, hxs, hyUx⟩ := mem_iUnion₂.mp hyU
    exact hUsub x hxs ⟨hyUx, hyc⟩

/-- A locally compact subgroup of a Hausdorff topological group is closed. -/
theorem Subgroup.isClosed_of_locallyCompactSpace {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T2Space G] (H : Subgroup G) [LocallyCompactSpace H] :
    IsClosed (H : Set G) := by
  obtain ⟨U, Z, hUopen, hZclosed, hUZ⟩ := IsLocallyClosed.of_locallyCompactSpace (H : Set G)
  -- normalize the decomposition: `H = U ∩ closure H`
  have hH : (H : Set G) = U ∩ _root_.closure (H : Set G) := by
    apply subset_antisymm
    · intro h hh
      exact ⟨(hUZ ▸ hh : h ∈ U ∩ Z).1, _root_.subset_closure hh⟩
    · rintro y ⟨hyU, hyc⟩
      have hclZ : _root_.closure (H : Set G) ⊆ Z :=
        closure_minimal (fun h hh => (hUZ ▸ hh : h ∈ U ∩ Z).2) hZclosed
      rw [hUZ]
      exact ⟨hyU, hclZ hyc⟩
  -- membership in the topological closure, as a subgroup
  have hmem_cl : ∀ {z : G}, z ∈ _root_.closure (H : Set G) → z ∈ H.topologicalClosure := by
    intro z hz
    rwa [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
  -- the complement of `H` in its closure is covered by the translates `z • U` with
  -- `z ∈ closure H \ H`, and each such translate avoids `H`.
  set V : Set G := ⋃ z ∈ _root_.closure (H : Set G) \ (H : Set G), z • U with hV
  have hVopen : IsOpen V := isOpen_biUnion fun z _ => hUopen.smul z
  have hdisj : ∀ w ∈ V, w ∈ _root_.closure (H : Set G) → w ∉ (H : Set G) := by
    rintro w hwV hwcl hwH
    obtain ⟨z, hz, hwzU⟩ := mem_iUnion₂.mp hwV
    obtain ⟨u, huU, rfl⟩ := hwzU
    simp only [smul_eq_mul] at hwcl hwH
    -- `u = z⁻¹ * (z * u) ∈ closure H ∩ U = H`, hence `z ∈ H`, contradiction
    have hucl : u ∈ _root_.closure (H : Set G) := by
      have hu : z⁻¹ * (z * u) ∈ H.topologicalClosure :=
        mul_mem (inv_mem (hmem_cl hz.1)) (hmem_cl hwcl)
      rw [inv_mul_cancel_left] at hu
      rwa [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hu
    have huH : u ∈ H := by
      have : u ∈ U ∩ _root_.closure (H : Set G) := ⟨huU, hucl⟩
      rwa [← hH, SetLike.mem_coe] at this
    have hwH' : z * u ∈ H := by rwa [SetLike.mem_coe] at hwH
    have hzH : z ∈ H := by
      have := H.mul_mem hwH' (H.inv_mem huH)
      rwa [mul_inv_cancel_right] at this
    exact hz.2 hzH
  have hcover : _root_.closure (H : Set G) \ (H : Set G) ⊆ V := by
    intro z hz
    have h1U : (1 : G) ∈ U := by
      have : (1 : G) ∈ U ∩ _root_.closure (H : Set G) := by
        rw [← hH]
        exact H.one_mem
      exact this.1
    exact mem_biUnion hz ⟨1, h1U, by simp⟩
  -- conclude: `H = closure H ∩ Vᶜ` is closed
  have hkey : (H : Set G) = _root_.closure (H : Set G) ∩ Vᶜ := by
    apply subset_antisymm
    · intro h hh
      exact ⟨_root_.subset_closure hh, fun hhV => hdisj h hhV (_root_.subset_closure hh) hh⟩
    · rintro y ⟨hyc, hyV⟩
      by_contra hyH
      exact hyV (hcover ⟨hyc, hyH⟩)
  rw [hkey]
  exact isClosed_closure.inter hVopen.isClosed_compl

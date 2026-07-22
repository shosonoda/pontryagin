import Mathlib.Topology.Algebra.PontryaginDual

open scoped Pointwise

/- Replace the `sorry` below with a complete proof. The statement must remain
identical to the one in `Challenge.lean`. -/
theorem pontryagin_duality (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G),  -- topological group iso
      ∀ g χ, e g χ = χ g := by
  sorry

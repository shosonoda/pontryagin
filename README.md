# pontryagin

A formalization challenge: **Pontryagin duality for locally compact abelian groups**, in Lean 4 / Mathlib, verified with [leanprover/comparator](https://github.com/leanprover/comparator).

> **Status: solved.** [`Solution.lean`](Solution.lean) proves the challenge theorem with no
> `sorry`, using only the permitted axioms (`propext`, `Classical.choice`, `Quot.sound`).
> The proof (~14,000 lines under [`Pontryagin/`](Pontryagin/)) follows the classical
> analytic route — L¹ convolution algebra, Gelfand spectrum, Bochner's theorem via
> positive functionals, the dual Haar measure, Fourier inversion, and Plancherel theory —
> with no σ-compactness or second-countability assumptions. See [`PLAN.md`](PLAN.md) for
> the architecture and `data/` for the proof blueprint.

## The challenge

[`Challenge.lean`](Challenge.lean) states the goal:

```lean
theorem pontryagin_duality (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G),  -- topological group iso
      ∀ g χ, e g χ = χ g := by
  sorry
```

That is: for every locally compact Hausdorff abelian topological group `G`, the canonical evaluation map `g ↦ (χ ↦ χ g)` is an isomorphism of topological groups onto the double Pontryagin dual.

## Instructions for formalization agents

Your task is to prove this theorem. Concretely:

1. **Work in [`Solution.lean`](Solution.lean).** Replace its `sorry` with a complete proof. The theorem name (`pontryagin_duality`) and its statement must remain *character-for-character identical* to `Challenge.lean` — the comparator checks that the solution proves the exact statement of the challenge, so do not "simplify", reorder binders, or restate it.
2. **Do not modify** `Challenge.lean`, `config.json`, `lakefile.toml`, `lake-manifest.json`, or `lean-toolchain`. Only `Solution.lean` (and any helper modules it imports — but keep everything reachable from `Solution.lean`) counts as your submission.
3. **Axiom budget:** your proof may only (transitively) use the axioms `propext`, `Quot.sound`, and `Classical.choice` — i.e. ordinary classical Mathlib reasoning. No `sorry`, no `native_decide`, no extra `axiom` declarations.
4. **Toolchain:** Lean `v4.32.0` with Mathlib `v4.32.0`, as pinned by `lean-toolchain` and `lakefile.toml`. Run `lake exe cache get` once before building, then `lake build Solution` to check your work locally.

### Reference material

The [`data/`](data/) folder contains a detailed proof blueprint written specifically for this autoformalization task:

- [`data/pontryagin_duality_mathlib.tex`](data/pontryagin_duality_mathlib.tex) / [`data/pontryagin_duality_mathlib.pdf`](data/pontryagin_duality_mathlib.pdf) — a paper-level proof of Pontryagin duality broken into Mathlib-ready lemmas, with notes on which ingredients already exist in Mathlib and which must be built.

Existing partial work lives in [`Pontryagin/Basic.lean`](Pontryagin/Basic.lean): the evaluation homomorphism `PontryaginDual.eval : A →ₜ* PontryaginDual (PontryaginDual A)` for locally compact `A`, a helper for producing the inverse from bijectivity + openness, and a complete proof of the duality for **finite discrete** groups (`PontryaginDual.dualityEquiv`). You may import and build on this module.

## Verification with comparator

Submissions are judged by [comparator](https://github.com/leanprover/comparator), which independently confirms that `Solution.lean` proves the exact challenge statement, within the permitted axioms, and passes kernel replay. The setup follows comparator's conventions:

- [`config.json`](config.json) — names the challenge/solution modules, the theorem to check, and the permitted axioms.
- `Challenge` and `Solution` are both `lean_lib` targets in [`lakefile.toml`](lakefile.toml).

To run the check (Linux, with `landrun` and `lean4export` in `PATH` — see the comparator README for the full trust model and the recommended `systemd-run` wrapper):

```sh
lake exe cache get
lake env path/to/comparator/binary config.json
```

Comparator builds and exports both modules inside a sandbox, verifies the statements match declaration-for-declaration, checks the axiom usage of `pontryagin_duality` in the solution, and replays the solution environment through the Lean kernel. Exit code 0 means the proof is accepted.

> **Note for judges:** never build `Solution.lean` (or run anything from an untrusted submission) outside the comparator sandbox before judging — a malicious build step could compromise the checking environment.

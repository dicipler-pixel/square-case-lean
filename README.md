<div align="center">

# The Square Case — four-body wall proofs in Lean

**Machine-checked finite algebra behind the four-body binary wall and the square lineage, checked by the Lean kernel on every push.**

[![Lean proof check](https://github.com/dicipler-pixel/square-case-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/square-case-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-63-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.21855590-blue)](https://doi.org/10.5281/zenodo.21855590)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.20818168-blue)](https://doi.org/10.5281/zenodo.20818168)

Jeromie Beasley

</div>

---

## The idea in one line

A binary-collision wall in four-body shape space is the zero set of `σ_L(W) = L W Lᵀ`.
The intrinsic flow `H ↦ T H + H T − Tr(T H) W` keeps a tangent on the wall whenever the
collision row `L` is an eigenrow of the inertia tensor `T`, and a commutator correction
`Ω W − W Ω` never pushes it off. For a positive-semidefinite `W` the wall equation alone
puts `L` in the kernel, so no separate null-vector assumption is needed.

## Start here

| If you want to… | Open |
| :--- | :--- |
| See the paper's own transport theorems | [`SquareCase/Transport.lean`](SquareCase/Transport.lean) |
| See the wall theorem | [`FourBodyWallInvariant.lean`](OperatorFirst/FourBodyWallInvariant.lean) |
| See why positive semidefiniteness is enough | [`FourBodyPSDWallBridge.lean`](OperatorFirst/FourBodyPSDWallBridge.lean) |
| Know exactly what is **not** proved | [`LIMITATIONS.md`](LIMITATIONS.md) |
| Check where every file came from | [`PROVENANCE.md`](PROVENANCE.md) |
| See the statements that must be rejected | [`FalseControls/`](FalseControls/) |

## What is proved

| File | Theorems | Result |
| :--- | :-: | :--- |
| [`FourBodyWallInvariant`](OperatorFirst/FourBodyWallInvariant.lean) | 9 | `σ_L` is linear; the wall line `W + tH` stays on the wall; the raw intrinsic term and the commutator correction both preserve the wall tangent (`intrinsic_preserves_wall_tangent`) |
| [`FourBodyPSDWallBridge`](OperatorFirst/FourBodyPSDWallBridge.lean) | 3 | For `W ⪰ 0`: `L W Lᵀ = 0 ⇔ W L = 0`, so the tangent theorem needs only the wall equation |
| [`ProjectionTraceBridge`](OperatorFirst/ProjectionTraceBridge.lean) | 5 | `‖P − Q‖²_F = Tr P + Tr Q − 2 Tr(PQ)` for orthogonal projections; equal rank `k` gives `Tr(PQ) = k − ½‖P − Q‖²_F` |
| [`HypersurfaceSquareLineage`](OperatorFirst/HypersurfaceSquareLineage.lean) | 26 | Inverse-gap-square response, Snell ⇔ squared metric Snell, rank-one projector distance `2 sin²θ`, fold/Gram fourth-power rigidity `1/s⁴`, three-body `sec⁴θ`, reduced four-body wall map, orientation weight |
| [`SquareCase/Transport`](SquareCase/Transport.lean) | 10 | From the paper itself: the Gram invariant (Prop. 2.1), the forced coefficient `c = 2` (Lemma 5.2), the eigenvalue block (Prop. 5.4), symmetrisation `D_t − g tᵀ = S(D_t − uuᵀ)S⁻¹` (Thm. 5.6), the eigenframe spectrum `tᵢ + tⱼ` (Thm. 6.1), and secular-equation eigenvectors (Thm. 6.2) |
| [`SquareCase/Secular`](SquareCase/Secular.lean) | 10 | Theorem 6.2: every eigenvalue off the `tᵢ` solves the secular equation `Σ gᵢtᵢ/(tᵢ − μ) = 1`; the secular function strictly increases across each gap and runs from `−∞` to `+∞` between consecutive poles; so **every gap holds exactly one eigenvalue**, with eigenvector `gᵢ/(tᵢ − μ)` |
| **Total** | **63** | |

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: three deliberately false statements must fail to compile, and fail
   for a mathematical reason. This shows the checker can say no.

To check it yourself with Lean installed:

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## The papers

- *The Square Case: Gram Reduction and Spectral Transport for N = d + 1 Bodies*, Jeromie
  Beasley. DOI [10.5281/zenodo.21855590](https://doi.org/10.5281/zenodo.21855590).
- *5D Spectral Anatomy of Four-Body Obstructions*, Jeromie Beasley. DOI
  [10.5281/zenodo.20818168](https://doi.org/10.5281/zenodo.20818168).

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released under the [MIT License](LICENSE) and the written text under [CC BY 4.0](LICENSE-CC-BY-4.0.md); see [`LICENSING.md`](LICENSING.md). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).

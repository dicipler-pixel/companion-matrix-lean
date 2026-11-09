<div align="center">

# The Companion-Matrix Projector Diagnostic — Lean proofs

![Lean](https://img.shields.io/badge/Lean-v4.36.0--rc2-blue)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.21787207-blue)](https://doi.org/10.5281/zenodo.21787207)

Jeromie Beasley

</div>

---

Lean 4 / Mathlib formalization of the core theorems of

> Jeromie Beasley, *The Companion-Matrix Projector Diagnostic: An Exact Order-2 Theorem, a
> Convergence Criterion, and a Complete Calibration Against the Ramanujan Machine Challenge
> Proofs*, August 2026. Zenodo concept DOI
> [10.5281/zenodo.21787207](https://doi.org/10.5281/zenodo.21787207); this library follows the
> latest version, [10.5281/zenodo.21799194](https://doi.org/10.5281/zenodo.21799194).

The diagnostic follows the top right singular vector `v₁(N)` of the transport
`Φ_N = T(N) ⋯ T(1)` of a linear recurrence, and the non-normality
`Φ(P) = ½‖[P, Pᵀ]‖²_F` of the Frobenius-normalized transport `P_N = Φ_N / ‖Φ_N‖_F`.

## What is proved

Everything below is proved with no `sorry` and only the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); see `scripts/Axioms.lean`.

| Result | Lean name | File |
|---|---|---|
| Lemma A identity `½‖[P,Pᵀ]‖²_F = ‖PPᵀ‖²_F − ‖P²‖²_F` | `phi_eq` | `LemmaA.lean` |
| Lemma A(i): `0 ≤ Φ(P) ≤ 1` when `‖P‖_F = 1` | `phi_nonneg`, `phi_le_one`, `phi_mem_Icc` | `LemmaA.lean` |
| Lemma A(ii): `Φ(xyᵀ) = 1 − (x·y)²` for unit `x, y` | `phi_vecMulVec` | `LemmaA.lean` |
| Lemma B: rank-one perturbation, `‖b‖ − 2η ≤ |⟨b, v⟩|`, and the left-vector version | `lemmaB`, `lemmaB_cos`, `lemmaB_left` | `LemmaB.lean` |
| Theorem 2 (positive half of Proposition 2): strict dominance ⇒ `v₁(N)` converges to the line of the dominant-coefficient functional; ties among non-dominant modes play no role | `theorem2`, `tendsto_of_rankOne_approx`, `inner_coordVec_of_ne` | `Dominance.lean` |
| Theorem 1 (order 2): `v₁(N)` converges to the line of the Casoratian dual `(−f₋₁, f₀)` of the minimal seed | `theorem1`, `transport_mulVec` | `Order2.lean` |
| Theorem 1, `Φ∞`: if `d_N/d_{N−1} → ρ` then `Φ(P_N) → 1 − (x̂∞·v̂∞)²`, `x∞ = (ρ, 1)`; also `ρ = ±∞` with `x∞ = (1, 0)` | `theorem1_phi`, `theorem1_phi_infty`, `tendsto_psi_transport` | `Order2Phi.lean` |

Mathlib has no singular vectors, so a *top right singular vector* of `A` is defined as a unit
vector maximizing `‖A w‖` on the unit sphere (`IsTopSingular`); this is the variational
definition. Since singular vectors are only defined up to sign, "converges" means convergence
of the line: `|⟨c, v₁(N)⟩| / ‖c‖ → 1`.

## What is stated but not proved

`CompanionMatrix/Statements.lean` holds statements only (as `Prop`s, never as theorems):

* `Theorem1LeftVector`: the left singular vector `u₁(N)` converges to the line of `x∞`.
  The proved `Φ∞` limit does not use it.

Not formalized: the negative half of Proposition 2, the Kronecker-product result, the
Casoratian pairing, the curvature results, and all numerical facts.

## Where the Lean statements differ from the paper's wording

* **Convergence is of lines, not vectors.** The paper writes `lim v₁(N) = normalize(−f₋₁, f₀)`;
  singular vectors are only defined up to sign, so the theorem is stated up to sign.
* **Theorem 1 hypotheses.** Only one complementary solution `d` is needed, with seed independent
  of `f`'s, `d_n ≠ 0` eventually, and `f_n/d_n → 0`. No Poincaré–Perron hypothesis is used and
  `T(n)` need not be invertible. The conclusion does not mention `d`, which is the paper's
  "independent of which complementary solution is used".
* **Proposition 2.** Only the positive half (strict dominance ⇒ convergence) is a theorem here.
  The abstract's "converges *precisely* when…" is not claimed.
* **Lemma B.** The hypothesis `η < ‖b‖/2` is not needed; without it the bound is just weaker.
* Lemma A and Lemma B are the two lemmas that fill the gap in the paper's proof of Theorem 1
  ("maximizing converges to maximizing a fixed functional" needs a uniform estimate).

**Indexing.** Lean sequences start at `0`, so a solution is stored shifted by one: `u k` is
`u_{k−1}`. The recurrence `u_n = a_n u_{n−1} + b_n u_{n−2}` reads
`u (n+2) = a (n+1) * u (n+1) + b (n+1) * u n`, and the seed `(u_0, u_{−1})` is `(u 1, u 0)`.

## Build

```bash
lake exe cache get   # prebuilt Mathlib
lake build
./scripts/check_axioms.sh
```

Pinned: Lean `v4.36.0-rc2`, Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`
(see `lake-manifest.json`). CI (`.github/workflows/build.yml`) builds every module, replays each
in `leanchecker`, rejects any `sorry`/`admit`/`native_decide`/new axiom, and runs the axiom audit.

## AI use

The mathematics is Jeromie Beasley's. The Lean code was written with Grok Bot
(Lean Green PR Machine). Every proof is checked by the Lean kernel.

## Author

Jeromie Beasley
* ORCID: https://orcid.org/0009-0006-4645-5643
* GitHub: [dicipler-pixel](https://github.com/dicipler-pixel)
* X: [@d1c1pler](https://x.com/d1c1pler)
* YouTube: [@AtlasMemoriae](https://www.youtube.com/@AtlasMemoriae)
* Site: [atlas-memoriae.dicipler.workers.dev](https://atlas-memoriae.dicipler.workers.dev)

## License

Code: MIT (`LICENSE`). Text (README and other prose): CC BY 4.0 (`LICENSE-CC-BY-4.0.md`).

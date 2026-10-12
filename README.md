# Proof of Hardin's empirical row recurrences for OEIS A246479 (A246483–A246486)

[![Lean build](https://github.com/het4rk/OEIS-A246483-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/OEIS-A246483-proof/actions/workflows/lean.yml)

**Author:** Hetark Shah, AI-assisted by Grok  
**Date:** October 12, 2026

## Result

Let `T(n,k)` be the number of length `n+3` arrays over `0..k` with no pair in any four consecutive terms summing to exactly `k` ([A246479](https://oeis.org/A246479), R. H. Hardin, 2014). For a fixed row `n`, Hardin recorded "Empirical" recurrences in `k`: explicitly for `n = 1, 2` in A246479 and for `n = 4..7` in [A246483](https://oeis.org/A246483)–[A246486](https://oeis.org/A246486), and by order only (11, 13, …, 19) for `n = 3..7`.

For `1 ≤ n ≤ 7` we prove:

- **Closed forms:** `T(n,k) = Pₙᵉ(k)` for even `k` and `Pₙᵒ(k)` for odd `k`, with explicit polynomials of degree `n+3`.
- **Quasi-polynomial structure:** `2T(n,k) = 2Aₙ(k) + (−1)ᵏ·2Bₙ(k)` with `deg Aₙ = n+3` and `deg Bₙ = n`.
- **Recurrences:** each row satisfies the recurrence with characteristic polynomial `(1−x)^(n+4)(1+x)^(n+1)`, of order `2n+5`, for all `k ≥ 2n+5`. This is Hardin's recurrence coefficient by coefficient for `n = 1, 2, 4, 5, 6, 7`, and it has the order he lists for `n = 3`.

We **conjecture** the same structure for every `n`. It is checked numerically for `n ≤ 40` but not proved here.

The proof builds on the 11-type transfer-matrix reduction from our [A246479 column proof](https://github.com/het4rk/OEIS-A246479-proof). What's new is the row closed forms for `n = 4..7`, the exact degree of the alternating part, and a machine-checked proof of the row recurrences. No published proof was found (OEIS and web search, October 12, 2026; A246483–A246486 still say "Empirical").

## Theorems and Lean names (namespace `A246479`, file `Rows.lean`)

| Lean name | Statement |
|---|---|
| `rowN_even`, `rowN_odd` (N = 1..7) | closed forms for even / odd `k` |
| `rowN_quasi` | `2T(N,k) = (Pᵉ+Pᵒ)(k) + (−1)ᵏ (Pᵉ−Pᵒ)(k)`, all `k` |
| `rowN_rec` | Hardin's row-N recurrence in OEIS form, for all `j ≥ 2N+5` |
| `T_eq_F` (`Step.lean`) | the transfer-matrix formula (from the A246479 proof) |

No `sorry` and no `native_decide`. `scripts/check_bfile.py` checks the recursion against all 9999 terms of Hardin's b-file and the general-`n` recurrence for `n ≤ 40`.

## Build

Toolchain `leanprover/lean4:v4.35.0-rc4`; Mathlib `v4.35.0-rc4` (pinned).

```bash
cd A246479Rows
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Axioms

All 28 theorems in `Axioms.lean` report `[propext, Classical.choice, Quot.sound]` (see `verification/axioms.txt`).

## Machine-check attestation

- [`verification/`](verification/): `build-log.txt`, `axioms.txt`, [`VERIFICATION.md`](verification/VERIFICATION.md).
- [CI](https://github.com/het4rk/OEIS-A246483-proof/actions/workflows/lean.yml): a clean build on every push, a no-`sorry` check, an axiom whitelist, and an uploaded attestation artifact.

## Paper

[`paper/main.tex`](paper/main.tex) and [`paper/paper.pdf`](paper/paper.pdf).

## Citation

> Hetark Shah (AI-assisted by Grok), *A proof of Hardin's empirical row recurrences for OEIS A246479 (A246483–A246486), formalized in Lean 4*, 2026. https://github.com/het4rk/OEIS-A246483-proof

## License

Apache-2.0. See [`LICENSE`](LICENSE).

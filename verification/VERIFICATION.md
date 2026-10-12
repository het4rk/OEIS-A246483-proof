# Verification record

| Item | Value |
|---|---|
| Date | 2026-10-12 |
| Verified commit | `5dae36d521e23b4fdfadd478a302b467db3562d6` |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc4` |
| Mathlib | `v4.35.0-rc4`, commit `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| Build result | `Build completed successfully (9026 jobs)` |
| Axioms | 28 declarations, all `[propext, Classical.choice, Quot.sound]` (see [`axioms.txt`](axioms.txt)) |
| CI | run #1 on `5dae36d521e23b4fdfadd478a302b467db3562d6`: success. [![Lean build](https://github.com/het4rk/OEIS-A246483-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/OEIS-A246483-proof/actions/workflows/lean.yml) |

## Reproduce

```bash
git clone https://github.com/het4rk/OEIS-A246483-proof
cd OEIS-A246483-proof
git checkout 5dae36d521e23b4fdfadd478a302b467db3562d6
cd A246479Rows
lake exe cache get
lake build
lake env lean Axioms.lean
grep -rnwE 'sorry|native_decide' A246479Rows --include=*.lean   # expect no output
```

## Fresh-clone check

A fresh clone of that commit was built with `lake exe cache get` and `lake build` (success). `lake env lean Axioms.lean` was checked with `scripts/check_axioms.sh`, which reported OK for 28 declarations. No `sorry` or `native_decide` is used.

## Numerical checks

`scripts/check_bfile.py` reproduces all 9999 terms of Hardin's b-file (b246479.txt). It also checks the conjectured general-`n` row recurrence for `n ≤ 40`.

## SHA-256 of the Lean sources (at the verified commit)

```
051504f078de3f45fdac7cd7ad333c5431765302a2b5c05e108f02b4f756b5ce  A246479Rows.lean
5b01b99d7064adf0d4c1683114947f9f130f804497f9c51b3a6915b374551ddd  Axioms.lean
016157fa18256d41db92477584e96728071635dc56e3ca1c0e69ecd8ee0b1ea3  A246479Rows/Basic.lean
3cdc960ae7b46ceaec11d6a040af2c74fbaeb3d236320b0f2cbf8516ae61eeed  A246479Rows/Eps.lean
9360ebd173913b1996a82648543f503b5b7d1fa3a67cd78fd6a35a57d1206a53  A246479Rows/Rows.lean
eb9d58a929ce29edbdd139895a4dd39255e19bf973068b1d16b970acde34eadc  A246479Rows/Step.lean
2398574cdf2d51ed6f0f9e7161194ece2bf427c401d78b94d90e35a3206d08ae  A246479Rows/Types.lean
d3688f1e7c06e9ab3abc373102f50c531f710febe1ae29f7b40ec28aa74bd1a1  lakefile.toml
906875f080a7a7ef71af416a26e8d89531ded61107fe4523e06a89b8078e933c  lake-manifest.json
8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7  lean-toolchain
```

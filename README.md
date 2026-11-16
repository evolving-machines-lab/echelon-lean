# echelon-lean

Lean 4 proofs for the Echelon technical report. Echelon is a rank-`r` replacement for Muon's
Newton–Schulz step: its update is an orthogonalized head on a tracked subspace plus a scaled tail. In
the code the update is still called `htDir` and the module `HeadTail` (identifiers keep the older
"head–tail" prefix).

The paper will be on hexagonmath (link to come).

## What the library proves

- **Convergence.** Any update that keeps a fixed fraction of the nuclear norm of the momentum (alignment
  at least `α‖M‖_*`) and has spectral norm at most `β` reaches Muon's `O(1/√T)` rate; only the constants
  change. Echelon meets this with `β = √2` for any orthonormal frame, and with `β = 1` after one cubic
  polishing step.
- **Muon itself.** Five Newton–Schulz steps on `M/‖M‖_F` never exceed spectral norm 1.25.
- **Cost.** Exact flop counts: Echelon at rank 16 uses at least 1000× fewer flops than five
  Newton–Schulz steps on a 4096×4096 layer.
- **Separation.** On a spiked 4096×4096 spectrum, Muon's update scores at most 0.57 while rank-1
  Echelon scores 1.
- **Refutations.** Three claims about Newton–Schulz from a popular write-up are false (contraction on
  [0.5, 1.5], five-step accuracy, fewer flops than an SVD).
- **Pilot.** The certificate score alone does not determine one-step progress on a quadratic; the best
  one-step decrease is `κ²‖G‖_*²/(2·srank d)`.

No proof uses `sorry` (it would show up as the axiom `sorryAx`), and every audited theorem depends only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The 35 audited theorems of the library
are the ones listed in `Axioms.lean`; the pilot file ends with its own `#print axioms` lines.

## Theorem map

Section and theorem numbers refer to the current version of the report (Section 4, "Theory: proofs a
machine checked").

| Lean theorem | File | Report |
|---|---|---|
| `FastMuon.Geometry.muon_family_rate` | `FastMuon/Certificate.lean` | Thm 1 (Certified-direction rate), §4.2; pinned, §4.3 |
| `FastMuon.Spectral.ht_muon_rate` | `FastMuon/Spectral.lean` | Thm 2 (Rate for Echelon), §4.2; pinned, §4.3 |
| `FastMuon.HeadTail.htDir_norm_le_sqrt_two` | `FastMuon/HeadTail.lean` | Thm 3 (Stability under any frame), §4.2; pinned, §4.3 |
| `FastMuon.HeadTail.htDir_norm_sq_le` | `FastMuon/HeadTail.lean` | bound behind Thm 3 |
| `FastMuon.Polish.polished_ht_norm_le_one` | `FastMuon/Polish.lean` | Thm 4 (Polishing), §4.2 |
| `FastMuon.Polish.polished_ht_norm_le_one_robust` | `FastMuon/Polish.lean` | Thm 4, robust form (τ low by up to √3) |
| `FastMuon.Spectral.ht_alignment_lower` | `FastMuon/Spectral.lean` | Thm 5 (Alignment given up), §4.2 |
| `FastMuon.NSMatrix.muon_norm_le` | `FastMuon/NSMatrix.lean` | Thm 6 (Muon's overshoot), §4.2; pinned, §4.3 |
| `FastMuon.NSPoly.muon_five_steps` | `FastMuon/NSPoly.lean` | Thm 6, scalar part |
| `FastMuon.Cost.speedup` | `FastMuon/Cost.lean` | Thm 7 (Flop counts), §4.2; pinned, §4.3 |
| `FastMuon.Cost.speedup_unbounded` | `FastMuon/Cost.lean` | Thm 7 |
| `FastMuon.Cost.speedup_4096_16` | `FastMuon/Cost.lean` | Thm 7 and Table 5 (main results); pinned, §4.3 |
| `FastMuon.Cost.speedup_4096_16384_32` | `FastMuon/Cost.lean` | Thm 7 |
| `FastMuon.Separation.ns5_spiked_kappa` | `FastMuon/Separation.lean` | Thm 8 (Spiked-spectrum separation), §4.2; pinned, §4.3 |
| `FastMuon.Separation.ht_spiked_kappa` | `FastMuon/Separation.lean` | Thm 8 |
| `FastMuon.MuonVsSVD.claimed_contraction_false` | `FastMuon/MuonVsSVD.lean` | §4.4 (refuted claim 1); pinned, §4.3 |
| `FastMuon.MuonVsSVD.claimed_five_step_false` | `FastMuon/MuonVsSVD.lean` | §4.4 (refuted claim 2) |
| `FastMuon.MuonVsSVD.five_steps_from_one_not_close` | `FastMuon/MuonVsSVD.lean` | §4.4 (refuted claim 2) |
| `FastMuon.MuonVsSVD.claimed_efficiency_false` | `FastMuon/MuonVsSVD.lean` | §4.4 (refuted claim 3) |
| `FastMuon.MuonVsSVD.ns_vs_svd` | `FastMuon/MuonVsSVD.lean` | §4.4 (refuted claim 3); pinned, §4.3 |
| `O4.kappa_does_not_determine_decrease` | `Pilot/O4_Certificate.lean` | §4.5 (Pilot) |
| `O4.decrease_eq_kappa_srank` | `Pilot/O4_Certificate.lean` | §4.5 (Pilot); used in §7 |

The other pilot results summarized in §4.5 (odd-polynomial degree bound, step-count example, Muon vs
gradient descent, alignment floor, implicit bias) are described in the report but their Lean files are
not part of this repository.

## Layout

- `FastMuon/*.lean`, `FastMuon.lean`: the library (namespace `FastMuon`).
- `Axioms.lean`: `#print axioms` for the 35 audited theorems.
- `Pilot/O4_Certificate.lean`: the pilot result cited in §4.5 (imports only Mathlib).
- `ComparatorChallenges/`: the seven pinned statements for `lake comparator` (§4.3); see
  [`COMPARATOR.md`](COMPARATOR.md).
- `LICENSE`: Apache-2.0 for this repository's code.
- `THIRD_PARTY_LICENSES/`: license of third-party code (see below).

## Versions

- Lean `leanprover/lean4:v4.35.0` (`lean-toolchain`)
- Mathlib tag `v4.35.0` (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in `lake-manifest.json`)

## Build

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get        # download prebuilt Mathlib
lake build                # builds FastMuon and Pilot
lake env lean Axioms.lean # prints the axioms of the 35 audited theorems
```

Every line printed by `Axioms.lean` should read
`depends on axioms: [propext, Classical.choice, Quot.sound]`.

To check the pinned statements (needs `bwrap`, see `COMPARATOR.md`):

```sh
for c in ComparatorChallenges/*.json; do lake comparator --config "$c"; done
```

## Third-party code

`FastMuon/MatrixFacts.lean` contains one lemma (`psd_norm_le_trace`) copied, with whitespace and naming
adapted, from OpenAI's Lean repository (https://github.com/openai/math), which is licensed under the
Apache License, Version 2.0. Its license text is in `THIRD_PARTY_LICENSES/openai-math-Apache-2.0.txt`,
and the file's docstring records the source and the changes.

## License

Apache-2.0 (code); the technical report is CC BY 4.0. See [`LICENSE`](LICENSE).

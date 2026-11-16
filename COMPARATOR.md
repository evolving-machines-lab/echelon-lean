# Pinned statements: `lake comparator`

`lake build` plus `#print axioms` (in `Axioms.lean`) shows that the proofs compile and use only
`propext`, `Quot.sound` and `Classical.choice`. It does not show that they prove what the README says.
The challenges in `ComparatorChallenges/` close that gap. Each one is a module that imports **only
Mathlib**, restates the needed definitions word for word, and states the headline theorems with
`sorry`. `lake comparator` (built into Lake since Lean v4.35.0, so there is no `require`) then checks
four things:

- every named theorem in the real module has exactly the challenge's statement;
- every definition the statements mention (and everything those definitions use, proofs inside
  definitions included) is the same constant in both;
- the proofs use no axiom outside `permitted_axioms`;
- Lean's kernel accepts the exported proofs.

A reviewer only needs to read the challenge files, not the proofs.

| Config | Theorems pinned | Definitions restated (from) |
|---|---|---|
| `Certificate.json` | `FastMuon.Geometry.muon_family_rate` | `Geometry`, `Geometry.Smooth` (Certificate) |
| `Spectral.json` | `FastMuon.Spectral.ht_muon_rate` | `Geometry`, `Smooth`; `tail`, `htDir`, `frob` (HeadTail); `frobBilin`, `frobCLM`, `nuc`, `holder`, `geometry` (Spectral) |
| `HeadTail.json` | `FastMuon.HeadTail.htDir_norm_le_sqrt_two` | `tail`, `htDir` |
| `Cost.json` | `FastMuon.Cost.speedup`, `FastMuon.Cost.speedup_4096_16` | `nsCost`, `htCost` |
| `NSMatrix.json` | `FastMuon.NSMatrix.muon_norm_le` | `frobNorm` (MatrixFacts), `nsStep` |
| `MuonVsSVD.json` | `FastMuon.MuonVsSVD.claimed_contraction_false`, `FastMuon.MuonVsSVD.ns_vs_svd` | `nsP` (NSPoly), `nsCost` (Cost), `svdCost` |
| `Separation.json` | `FastMuon.Separation.ns5_spiked_kappa` | `nsP` (NSPoly) |

The solution module of each config is the matching `FastMuon.<Name>` module. `definition_names` is
empty, so no definition is a hole: the comparator compares each definition's body too, not only its
type.

## Run it

You need `bwrap` (bubblewrap) on PATH, or `COMPARATOR_BWRAP` set to its path. It also needs
unprivileged user namespaces, or a setuid-root `bwrap`. The comparator builds and exports both
modules inside that sandbox.

```sh
cd lean
lake build                                   # once; builds Mathlib deps + FastMuon
lake comparator --config ComparatorChallenges/Cost.json          # one challenge
for c in ComparatorChallenges/*.json; do                         # all of them
  echo "== $c"; lake comparator --config "$c"; echo "exit $?"
done
```

Exit codes: `0` means accepted, and the output ends with `Your solution is okay!`. `1` means
rejected: the statement or a definition differs, there is a forbidden axiom, or the kernel or the
build failed. `2` means the check could not start (no `bwrap`, bad config). Add `--paranoid` to also
run the checkers bundled with the toolchain (`leanchecker-paranoid`, `lean4lean`, `nanoda`,
`con-leche`, `con-ron`).

**On Ubuntu 24.04** `bwrap` is not installed by default, and AppArmor blocks unprivileged user
namespaces (`kernel.apparmor_restrict_unprivileged_userns = 1`), so the command exits `2`. There are
three ways to run it:

1. `sudo apt-get install bubblewrap`, then give `/usr/bin/bwrap` an AppArmor profile that allows
   `userns` (`/etc/apparmor.d/bwrap`, followed by `sudo apparmor_parser -r /etc/apparmor.d/bwrap`):

   ```
   abi <abi/4.0>,
   include <tunables/global>
   profile bwrap /usr/bin/bwrap flags=(unconfined) {
     userns,
   }
   ```

2. Run it on any machine where `bwrap` works.
3. Add `--inadvisably-no-sandbox` for a checkout you trust. Only the sandbox goes away; the
   statement, definition, axiom and kernel checks all still run.

## Negative test (shows the check is not vacuous)

```sh
sed 's/1000 \* htCost 4096/100 * htCost 4096/' ComparatorChallenges/Cost.lean > ComparatorChallenges/Scratch.lean
sed 's/ComparatorChallenges.Cost/ComparatorChallenges.Scratch/' ComparatorChallenges/Cost.json > scratch.json
lake comparator --config scratch.json   # expect exit 1: statement mismatch for FastMuon.Cost.speedup_4096_16
rm ComparatorChallenges/Scratch.lean scratch.json
rm -f .lake/build/lib/lean/ComparatorChallenges/Scratch.* .lake/build/ir/ComparatorChallenges/Scratch.*
```

The `ComparatorChallenges` lib uses `globs = ["ComparatorChallenges.+"]`, so a scratch file in that
folder is a buildable module. The lib is not a default target, so `lake build` still builds only
`FastMuon` and `Pilot`.

## Keeping it in sync

If a pinned statement or one of the restated definitions changes in `FastMuon/`, copy the change into
the challenge, keeping the text identical. Otherwise the comparator rejects. Binder names may differ:
the kernel-level comparison is up to alpha-equivalence.

## Verdicts (2026-11-08)

Run with `--inadvisably-no-sandbox` (no `bwrap` on the machine used): all seven challenges print
"Your solution is okay!" (exit 0). Negative test: a copy of `Cost` with `speedup_4096_16` weakened
from 1000× to 100× fails with "Challenge and solution theorem statement do not match" (exit 1); the
copy was deleted afterwards.

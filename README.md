# Lean verification of POMDP logging hardness

Lean formalization of the exact main theorem and minimax/sample-complexity results
in *Exponential Hardness of Off-Policy Evaluation under History-Dependent Logging*.
The proofs quantify over every stated horizon and sample size and include arbitrary
real-valued randomized estimators using complete logged trajectories.

**Start here:** [main theorem](PomdpLogging/MainTheorem.lean) ·
[claim-to-theorem map](STATUS.md) · [verification report](VERIFICATION.md) ·
[provenance](PROVENANCE.md)

## Quick start

Prerequisites: macOS or Linux (including WSL), Git, curl, tar, and ordinary compiler
tools. Python 3.9 or later is needed for the optional source/package checks.
The initial setup downloads several gigabytes of dependencies.

Extract the source archive or clone this repository, open a terminal in its root,
and run:

```sh
sh setup.sh
sh check.sh
```

`setup.sh` installs the toolchain locally under `.tools/`, retrieves the pinned
dependencies under `.lake/`, and downloads the official mathlib build cache. It
leaves shell startup files unchanged. Subsequent verification uses the local
installation. The [official mathlib instructions](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
describe the dependency-cache mechanism.

`check.sh` builds every mathematical module, then runs [Audit.lean](Audit.lean).
The audit rejects any project declaration whose transitive axioms include anything
outside `propext`, `Classical.choice`, and `Quot.sound`. The initial verified version
reports:

```text
Build completed successfully
Axiom audit passed: 1040 project declarations, 688 theorems.
Allowed dependencies: propext, Classical.choice, Quot.sound.
```

Counts include compiler-generated declarations. The original local fresh build and
audit passed; its record is [clean-build.log](clean-build.log). The GitHub workflow
has been provided for future runs and has not been run on a hosted repository as
part of this package preparation.

## What is verified?

- The exact main theorem, with action coverage `6`, physical-belief coverage `3`,
  uniform-prior revealing constant `35/9`, and prior-weighted constant `9`.
- The exact full-data KL lower bound at accuracy `1/8`, with all estimator
  randomization included.
- Both directions of the three-symbol experiment equivalence; exact minimax risk,
  majority-test attainment, and matching horizon/confidence sample bounds.
- The documented Appendix C/D results and deterministic-variant TV/minimax formulas.

**Scope:** the deterministic variant's additional revealing assertion and the compact
matrix's standalone row formulas are not separately formalized. They are not gaps
in the verified main theorem. See [VERIFICATION.md](VERIFICATION.md) for the complete
semantic correspondence and trust boundary. Literature novelty is not certified
by Lean. The manuscript itself is not included in this package.

## Pinned dependencies

| Component | Version |
|---|---|
| Lean | `leanprover/lean4:v4.34.0` |
| mathlib | `db00fb3901b1bb4954f8a2373285959a5930bbfa` |
| Transitive packages | Exact revisions in [lake-manifest.json](lake-manifest.json) |

Use the committed toolchain and manifest. Building this version does not require
running `lake update` or selecting a newer mathlib revision.

## Source integrity and releases

```sh
python3 scripts/package.py --check
python3 scripts/package.py --build
```

The first command verifies [SOURCE_SHA256SUMS](SOURCE_SHA256SUMS). The second creates
deterministic source ZIP and tar.gz archives, plus archive checksums, in `dist/`.
No installed tools, dependency caches, compiled files, or Git credentials are shipped.
For development and refreshing the manifest, see [CONTRIBUTING.md](CONTRIBUTING.md).

## Put this package on GitHub

The ZIP is a standalone repository source tree. Extract it and put its contents
at the root of a new repository, retaining the hidden `.github/` directory.
[The included workflow](.github/workflows/verify.yml) runs source-integrity checks,
installs the pinned dependencies, builds all proofs, and runs the axiom audit on
pushes and pull requests. It uses a fresh Linux runner and saves the verification log.
It can also be started manually from the Actions tab.

After making intentional edits, run `python3 scripts/package.py --update` and commit
the refreshed manifest. Repository visibility, ownership, and licensing are left
for the person publishing it; no license has been selected or included.

## Reference document

Title: *Exponential Hardness of Off-Policy Evaluation under History-Dependent Logging*.
Reference PDF: `pomdp_logging_hardness_conference.pdf` (18 pages), SHA-256:

```text
3b61b9425ddfa12f0d9a5fe7bf038c978234e2135ad0253ac68756cb7efb4c32
```

See [PROVENANCE.md](PROVENANCE.md) for AI-assisted development provenance and
[CHANGELOG.md](CHANGELOG.md) for the initial release contents.

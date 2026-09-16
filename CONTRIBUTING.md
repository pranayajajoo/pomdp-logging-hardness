# Contributing and reviewing

Start with [the main theorem](PomdpLogging/MainTheorem.lean),
[the statement mapping](STATUS.md), and [the verification report](VERIFICATION.md).
Check both the theorem statement and its connection to the manuscript's definitions.
Compilation alone cannot determine whether a formal statement models the intended claim.

## Verify a change

```sh
sh setup.sh
sh check.sh
```

Keep the pinned Lean version and dependency revisions unless the change explicitly
updates them. Do not use `lake update` merely to build the current source.

The build must succeed and `Audit.lean` must reject every dependency outside
`propext`, `Classical.choice`, and `Quot.sound`. Do not add unfinished proofs,
problem-specific axioms, or weaken statements to make a proof compile.

After intentional changes, update the source manifest and verify it:

```sh
python3 scripts/package.py --update
python3 scripts/package.py --check
```

Include the relevant formal statement, mathematical justification, and verification
result in a pull request. Update the statement map if the verification scope changes.
The GitHub workflow repeats the build and axiom audit on a fresh Linux runner.

## Create a source release

```sh
python3 scripts/package.py --build
```

This checks the manifest and creates ZIP and tar.gz archives in `dist/`, together
with `SHA256SUMS`. Archive metadata is deterministic. Toolchains, dependency caches,
compiled artifacts, Git metadata, and other workspace files are excluded.

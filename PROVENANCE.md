# Provenance and verification scope

This formalization was developed with OpenAI Codex assistance from the manuscript
*Exponential Hardness of Off-Policy Evaluation under History-Dependent Logging*.
It is intended for independent review and reproduction. The machine-checkable
evidence is the Lean source, its pinned dependencies, and the build/axiom audit.

Reference document: `pomdp_logging_hardness_conference.pdf`, 18 pages. SHA-256:

```text
3b61b9425ddfa12f0d9a5fe7bf038c978234e2135ad0253ac68756cb7efb4c32
```

The manuscript itself is not included in this source package. Its title and hash
identify the version whose statements were formalized. This repository does not
assign manuscript authorship or assert that the formalization was independently
reviewed by a human Lean expert.

[VERIFICATION.md](VERIFICATION.md) describes the semantic correspondence, standard
axioms, dependency-cache trust boundary, and auxiliary appendix claims outside the
formalization. [STATUS.md](STATUS.md) maps individual claims to theorem names.
The repository establishes no claim of literature priority.

`clean-build.log` is the original local clean-build record. The supplied GitHub
Actions workflow will produce fresh verification logs when the package is published
and run; no hosted CI run is claimed by this initial package.
Historical milestone audit files are retained for traceability. Mathematical source
files are unchanged by the initial GitHub packaging work.

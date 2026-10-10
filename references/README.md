# Reference dependencies

The `FormalConjectures*` files retain their original Apache 2.0 notices and are a frozen dependency closure for the exact original problem statements. `TaskSupport.lean` is from the Apache 2.0 Conjectures validator. Source hashes and revisions are in `PROVENANCE.json`; the license is included here. Mathlib and its transitive dependencies are pinned by the Lake manifest.

The reference files contain the original admitted conjecture declarations. Our solution files inspect their types and prove separate targets. Acceptance requires every final target’s axiom closure to exclude `sorryAx`; importing a problem declaration is not using its admitted proof.

The original service proof bodies are unmodified under `accepted/`; `Solutions/` supplies the original imports and namespace and adds inspection commands. The wrapper construction does not change the mathematical proof body.

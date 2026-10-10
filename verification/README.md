# Local Lean checks

## Complete Erdős 1062 — October 10, 2026

The complete target was checked from clean source commit
`ab42bf613bd773f78a0350c5869dcccfaab1faed`.
`Erdos1062Full.full_scope` combines the exact finite formula for every natural
`n` with convergence to the explicit irrational density. All nine exported
theorems have exactly `propext`, `Classical.choice`, and `Quot.sound` in their
complete transitive axiom closures.

- [Machine-readable report](erdos1062-full.json)
- [Full wrapper build log](erdos1062-full-build.log)
- [Fresh theorem and axiom inspection](erdos1062-full-axioms.log)
- [Initial fresh 791-second proof-module build](erdos1062-original-build.log)
- [Initial build metadata](erdos1062-original-build.json)
- [Pinned dependency revisions and clean-source check](dependency-revisions.json)

The original large module compiled afresh in a separate checkout. The following
full-wrapper run reused that compiled module and built the new wrapper; the
final audit freshly imported it and checked all exported theorem types and
axiom closures. The nine dependency repositories matched their pins and had no
tracked source modifications. Pinned Lean/Mathlib library binaries were reused;
this was not a clean rebuild of all libraries or a second-kernel check.

Reproduce with `python3 scripts/reproduce_erdos1062_full.py`. The report records
actual source hashes, compiler, commands, UTC timestamps and exit statuses.
The previously stopped optional 1062(ii) replay remains an incomplete historical
run; it is not retroactively counted as a pass.

## Earlier verification batch

The reports in this directory describe the exact accepted source bodies in commit `8b9db1d8c0ded5398d5e4e4bbdf8f2ec14ce5c23`. Each report records SHA-256 hashes, the compiler, command, exit status and complete printed target axiom closure. The selected source and wrapper bytes remain unchanged in later documentation commits.

Verified targets: Erdős 14(i), 14(ii), 108, 944 and 859. The recorded 14(i) run replayed its module cache after an initial fresh successful build; the other four reports show fresh target-module compilation. All reused precompiled dependencies from the pinned Mathlib version. Every reported target depends only on `propext`, `Classical.choice` and `Quot.sound`.

The reference conjecture files contain admitted problem declarations. Their compiler warnings are visible in the logs; the final target axiom closures do not include `sorryAx`. These logs do not claim that every declaration in the reference library has been proved.

Erdős 1062(ii) and the Szabó variant of 272 were not included in that earlier published set of completed local reports. The optional 1062(ii) local run was stopped before completion; no local pass is claimed. No new local run of 272 completed in this batch. The service records remain separate evidence for those targets. No second-kernel or new independent human mathematical review is claimed.

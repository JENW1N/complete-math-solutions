# Local Lean checks

The reports in this directory describe the exact accepted source bodies in commit `8b9db1d8c0ded5398d5e4e4bbdf8f2ec14ce5c23`. Each report records SHA-256 hashes, the compiler, command, exit status and complete printed target axiom closure. The selected source and wrapper bytes remain unchanged in later documentation commits.

Verified targets: Erdős 14(i), 14(ii), 108, 944 and 859. The recorded 14(i) run replayed its module cache after an initial fresh successful build; the other four reports show fresh target-module compilation. All reused precompiled dependencies from the pinned Mathlib version. Every reported target depends only on `propext`, `Classical.choice` and `Quot.sound`.

The reference conjecture files contain admitted problem declarations. Their compiler warnings are visible in the logs; the final target axiom closures do not include `sorryAx`. These logs do not claim that every declaration in the reference library has been proved.

Erdős 1062(ii) and the Szabó variant of 272 are not yet included in this published set of completed local reports. The service records remain separate evidence for those targets. No second-kernel or new independent human mathematical review is claimed.

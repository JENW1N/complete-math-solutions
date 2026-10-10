# Erdős 1062 complete-scope source provenance

The mathematical work and original formal development are credited to Liam
Kruer ([lkruer](https://github.com/lkruer)) and Jensen Kohlmeyer
([JENW1N](https://github.com/JENW1N)). This is their coauthor-controlled source
repository. The October 10, 2026 wrapper, source audit, reproduction script, and
submission documentation were prepared with Codex assistance at Jensen
Kohlmeyer's request. Repository ownership by itself is not offered as proof of
exclusive mathematical or formalization authorship.

The original accepted body is preserved byte for byte in
`accepted/erdos1062.lean` and `proofs/Erdos1062PartII.lean`:

- Size: 4,965,602 bytes.
- SHA-256: `2ebc87b06386daf9720ac037996ce87eb760dc58097cd098ec6620b1c7df92b6`.
- Original source edition baseline: `2fb37782da6f1f125c44bdd9cca5b2a205d9aad8`.
- [Public service record](https://conjectures.io/results/8d59a0af-6762-4606-93c9-72dd356a57bc).
- Download URL and other accepted-body hashes: `accepted/PROVENANCE.json`.

`Solutions/Erdos1062.lean` wraps that original body with the frozen reference
and type-extraction support. This edition suppresses style lint output for the
large replay. It does not replace proof checking or alter the accepted body.
`Solutions/Erdos1062Full.lean` exposes the internal exact formula as a direct
universal theorem and joins it with direct convergence and irrationality
statements. Its statements do not use the reference `answer` placeholder.

The September service acceptance and public certificate concern the original
part (ii) target. The full-scope wrapper and its verification are October work;
they are not backdated to that service record. See
[the scope note](notes/erdos1062-full-scope.md) for the exact mathematical target,
the distinct manuscript/exposition titles, earlier Lebensold and Davis results,
and the limits of historical evidence. No claim of exhaustive priority review,
prize acceptance, or award entitlement is made.

The selected toolchain is Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474` in the package manifest.
`verification/erdos1062-full.json`, when present, records the actual compiler,
source hashes, command exit statuses and complete transitive axiom closures.
It distinguishes local verification from the service record. Reproduction uses
pinned precompiled library dependencies; it is not a second-kernel check.

Reference files intentionally preserve their original admitted conjectures.
Those placeholders must not appear in the audited proof dependency closure.
The full proof's audit is the relevant evidence, rather than a grep claim that
the entire reference library is complete.

## Completed local verification

The clean proof commit `ab42bf613bd773f78a0350c5869dcccfaab1faed` passed
`lake build Solutions.Erdos1062Full` and
`lake env lean verification/Erdos1062FullAudit.lean` on October 10, 2026.
The final audit completed at 06:18:14.923305 UTC. All nine exported declarations,
including `Erdos1062Full.full_scope`, use exactly `propext`, `Classical.choice`,
and `Quot.sound`. See the [verification record](verification/erdos1062-full.json)
and [logs](verification/README.md). This evidence commit adds logs and
documentation without changing the selected proof sources.

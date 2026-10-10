#!/usr/bin/env python3
"""Build and audit the complete finite-formula and irrational-density theorem."""
import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification'
NAMES = ['g_cast', 'exact_formula_real', 'exact_formula', 'exact_formula_nat',
         'part_i', 'density_converges', 'density_irrational', 'part_ii', 'full_scope']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def run(command, path):
    started = utc()
    with path.open('w') as log:
        proc = subprocess.run(command, cwd=ROOT, text=True, stdout=log, stderr=subprocess.STDOUT)
    return {'command': command, 'started_utc': started, 'finished_utc': utc(),
            'exit_code': proc.returncode, 'log': path.name}

OUT.mkdir(exist_ok=True)
revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
worktree_status = subprocess.check_output(['git', 'status', '--short'], cwd=ROOT, text=True).splitlines()
compiler = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT, text=True).strip()
build = run(['lake', 'build', 'Solutions.Erdos1062Full'], OUT / 'erdos1062-full-build.log')
audit = run(['lake', 'env', 'lean', 'verification/Erdos1062FullAudit.lean'],
            OUT / 'erdos1062-full-axioms.log') if build['exit_code'] == 0 else None
closures = {}
if audit:
    text = (OUT / audit['log']).read_text()
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        closures[name] = [a.strip() for a in axioms.split(',') if a.strip()]
required = ['Erdos1062Full.' + n for n in NAMES]
clean = all(name in closures and set(closures[name]) <= ALLOWED for name in required)
complete = set(closures.get('Erdos1062Full.full_scope', [])) == ALLOWED
paths = ['accepted/erdos1062.lean', 'Solutions/Erdos1062.lean', 'Solutions/Erdos1062Full.lean',
         'verification/Erdos1062FullAudit.lean', 'FormalConjectures/ErdosProblems/1062.lean',
         'TaskSupport.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
record = {'source_commit_at_run': revision, 'worktree_status_at_run': worktree_status, 'compiler': compiler, 'build': build, 'audit': audit,
          'axiom_closures': closures, 'source_sha256': {
              p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths},
          'passed': build['exit_code'] == 0 and audit is not None and audit['exit_code'] == 0 and clean and complete,
          'limitations': 'Uses pinned precompiled Lean/Mathlib dependencies; this is ordinary Lean compilation and complete transitive axiom inspection, not a second-kernel or independent human mathematical review. The full formula and direct density statements are audited separately from the reference file, which contains admitted declarations.'}
(OUT / 'erdos1062-full.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
raise SystemExit(0 if record['passed'] else 1)

#!/usr/bin/env python3
"""Recheck the Mathlib-only Erdős 354 proof package against cached Lean dependencies."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
from datetime import datetime, timezone
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE
DEFAULT_LEAN = Path(shutil.which('lean') or 'lean')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, default=DEFAULT_LEAN)
    parser.add_argument('--workspace', type=Path, default=WORKSPACE,
                        help='Lake workspace containing the cached Mathlib dependency')
    parser.add_argument('--reuse', action='store_true',
                        help='reuse object files newer than their sources')
    args = parser.parse_args()
    lean = args.lean.resolve()
    lake = lean.with_name('lake')
    build = HERE / '.build'
    logs = HERE / 'logs'
    build.mkdir(exist_ok=True)
    logs.mkdir(exist_ok=True)
    dependencies = subprocess.check_output(
        [str(lake), 'env', 'printenv', 'LEAN_PATH'], cwd=args.workspace, text=True).strip()
    excluded = {str(args.workspace / '.lake/build/lib/lean'),
                str(args.workspace / '.formal-conjectures/.lake/build/lib/lean')}
    dependencies = os.pathsep.join(p for p in dependencies.split(os.pathsep) if p not in excluded)
    env = os.environ.copy()
    env['LEAN_PATH'] = str(build) + os.pathsep + dependencies
    (HERE / 'dependency-paths.txt').write_text(env['LEAN_PATH'] + '\n')
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    print(version, flush=True)
    modules = ['Erdos354Definitions', 'KohlmeyerKruerPartI', 'KitamuraPartII',
               'Combined', 'QuantifierObstruction', 'RecurrenceDecay', 'MultinacciBase',
               'MultinacciAsymptotic', 'MultinacciIntegers', 'ParameterExistence',
               'FullSolution', 'AuditDefinitions']
    results = []
    axiom_audit = {}
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    for module in modules:
        source = HERE / (module + '.lean')
        if not source.exists():
            raise FileNotFoundError(source)
        obj = build / (module + '.olean')
        log = logs / (module + '.log')
        if args.reuse and obj.exists() and obj.stat().st_mtime > source.stat().st_mtime:
            print('Reuse', module, flush=True)
            continue
        start = time.monotonic()
        command = [str(lean), '-o', str(obj), str(source)]
        print('Checking', module, flush=True)
        with log.open('w') as out:
            result = subprocess.run(command, cwd=HERE, env=env, stdout=out, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - start
        text = log.read_text()
        results.append({'module': module, 'exit_code': result.returncode,
                        'seconds': round(elapsed, 2),
                        'sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
        print(f'{module}: exit {result.returncode}, {elapsed:.1f}s', flush=True)
        unknown_axioms = set()
        for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S):
            used = [x.strip() for x in axioms.split(',') if x.strip()]
            axiom_audit[name] = used
            unknown_axioms.update(set(used) - allowed_axioms)
        if result.returncode or 'sorryAx' in text or 'warning:' in text or unknown_axioms:
            print(text, end='', flush=True)
            print('Verification failed.', flush=True)
            (HERE / 'verification.json').write_text(json.dumps({'status': 'failed', 'lean': version, 'modules': results, 'axiom_audit': axiom_audit}, indent=2) + '\n')
            return result.returncode or 1
        for line in text.splitlines():
            if 'depends on axioms:' in line:
                print(line, flush=True)
    (HERE / 'verification.json').write_text(json.dumps(
        {'status': 'passed', 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
         'lean': version, 'modules': results, 'axiom_audit': axiom_audit,
         'library_dependency': {'name': 'mathlib', 'revision':
             '0df444a360eaa60ab8c11dca51a86af692955474'},
         'formal_conjectures_runtime_dependency': False}, indent=2) + '\n')
    print('All requested modules verified.', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())

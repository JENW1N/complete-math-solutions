#!/usr/bin/env python3
"""Compile selected original accepted proof bodies and preserve honest audit logs."""
import argparse
import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = {
    'erdos14i': 'Erdos14i', 'erdos14ii': 'Erdos14ii', 'erdos108': 'Erdos108',
    'erdos944': 'Erdos944', 'erdos859': 'Erdos859', 'erdos1062': 'Erdos1062',
    'erdos272': 'Erdos272',
}

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('targets', nargs='*', choices=list(MODULES))
args = parser.parse_args()
targets = args.targets or list(MODULES)
out = ROOT / 'verification'
out.mkdir(exist_ok=True)
revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
compiler = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT, text=True).strip()
records = []
for key in targets:
    module = 'Solutions.' + MODULES[key]
    command = ['lake', 'build', module]
    print('Checking ' + key, flush=True)
    started = datetime.datetime.now(datetime.timezone.utc)
    proc = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    finished = datetime.datetime.now(datetime.timezone.utc)
    log = proc.stdout
    (out / (key + '.log')).write_text(log)
    source = ROOT / 'accepted' / (key + '.lean')
    wrapper = ROOT / 'Solutions' / (MODULES[key] + '.lean')
    lines = [line for line in log.splitlines() if "'Bounty.target' depends on axioms:" in line]
    expected_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
    closures = [re.search(r'depends on axioms: \[([^\]]*)\]', line) for line in lines]
    clean_axioms = bool(lines) and all(
        match is not None and {a.strip() for a in match.group(1).split(',')} == expected_axioms
        for match in closures
    )
    record = {
        'target': key, 'module': module, 'source_commit': revision, 'command': command,
        'started_utc': started.isoformat(), 'finished_utc': finished.isoformat(),
        'compiler': compiler, 'exit_code': proc.returncode,
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'wrapper_sha256': hashlib.sha256(wrapper.read_bytes()).hexdigest(),
        'axiom_output': lines, 'log': key + '.log',
        'fresh_module_build_reported': ('Built ' + module) in log,
        'cached_imports': True,
        'passed': proc.returncode == 0 and clean_axioms,
        'limitations': 'Uses pinned precompiled Mathlib dependencies. This is Lean compilation and a transitive target-axiom inspection, not a second-kernel check or an exhaustive review of the prose or historical priority.'
    }
    (out / (key + '.json')).write_text(json.dumps(record, indent=2) + '\n')
    records.append(record)
    print(json.dumps({'target': key, 'passed': record['passed'], 'seconds': (finished-started).total_seconds(), 'axioms': lines}), flush=True)
    if not record['passed']:
        print(log[-6000:], flush=True)
        raise SystemExit(1)
(out / 'summary.json').write_text(json.dumps(records, indent=2) + '\n')

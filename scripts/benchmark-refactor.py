#!/usr/bin/env python3
"""Compare leaf elaboration before/after the shared bounded-source refactor.

Run after `lake build`, with the unmodified baseline checkout as the argument.
Dependencies come from the current checkout in both cases. Only temporary
source/interface files are written; neither checkout is changed.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import tempfile
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('baseline', type=Path)
parser.add_argument('--rounds', type=int, default=3)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
if args.rounds < 1:
    parser.error('--rounds must be positive')
root = Path(__file__).resolve().parents[1]
baseline = args.baseline.resolve()
lake = os.environ.get('LAKE', 'lake')
lean_path = subprocess.check_output([lake, 'env', 'printenv', 'LEAN_PATH'], cwd=root, text=True).strip()
lean = subprocess.check_output([lake, 'env', 'which', 'lean'], cwd=root, text=True).strip()
modules = [Path('ComplexityOfGenerators/Simulation/ExactRecursive') / f'{name}.lean'
           for name in ['Trial', 'TrialBounds', 'Prepare']]
measurements = {'before': {str(p): [] for p in modules}, 'after': {str(p): [] for p in modules}}
with tempfile.TemporaryDirectory(prefix='generator-refactor-benchmark-') as scratch:
    scratch = Path(scratch)
    source = scratch / 'baseline'
    for module in modules:
        (source / module).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(baseline / module, source / module)
    for label in ['before', 'after']:
        shutil.copytree(root / '.lake' / 'build' / 'lib' / 'lean', scratch / label,
                        copy_function=lambda src, dst: os.symlink(src, dst))
    for _ in range(args.rounds):
        for label, source_root in [('before', source), ('after', root)]:
            build = scratch / label
            env = dict(os.environ, LEAN_PATH=str(build) + ':' + lean_path)
            for module in modules:
                target = (build / module).with_suffix('.olean')
                target.parent.mkdir(parents=True, exist_ok=True)
                target.unlink(missing_ok=True)
                started = time.perf_counter()
                checked = subprocess.run([lean, '-DautoImplicit=false', '-o', str(target), str(module)],
                                         cwd=source_root, env=env, text=True, capture_output=True)
                elapsed = time.perf_counter() - started
                if checked.returncode:
                    raise SystemExit(checked.stdout + checked.stderr)
                measurements[label][str(module)].append(elapsed)
report = {
    'rounds': args.rounds,
    'scope': 'fresh elaboration of three leaves, shared cached dependencies',
    'median_seconds': {label: {module: round(statistics.median(times), 3)
                              for module, times in rows.items()}
                       for label, rows in measurements.items()},
    'source_lines': {label: sum(len((source_root / module).read_text().splitlines()) for module in modules)
                     for label, source_root in [('before', baseline), ('after', root)]},
}
output = json.dumps(report, indent=2) + '\n'
print(output, end='')
if args.output:
    args.output.write_text(output)

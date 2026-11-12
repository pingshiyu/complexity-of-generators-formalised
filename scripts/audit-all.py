#!/usr/bin/env python3
"""Audit every local Lean source module after `lake build`."""
from pathlib import Path
import os
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
modules = sorted(
    '.'.join(path.relative_to(root).with_suffix('').parts)
    for path in (root / 'ComplexityOfGenerators').rglob('*.lean')
)
modules.append('ComplexityOfGenerators')
body = (root / 'scripts' / 'AuditFoundations.lean').read_text()
body = body[body.index('open Lean Elab Command'):]
with tempfile.TemporaryDirectory(prefix='generator-axiom-audit-') as scratch:
    audit = Path(scratch) / 'AuditAll.lean'
    audit.write_text(''.join(f'import {module}\n' for module in modules)
                     + 'import Lean.Util.CollectAxioms\n\n' + body)
    result = subprocess.run([os.environ.get('LAKE', 'lake'), 'env', 'lean', str(audit)], cwd=root)
    raise SystemExit(result.returncode)

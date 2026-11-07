#!/usr/bin/env python3
"""Local orchestration test using a fake Lake binary; NOT a Lean proof."""
import os
from pathlib import Path
import re
import subprocess
import tempfile
import shutil

SOURCE = Path(__file__).with_name('verify_track_d_locally.sh')
source = SOURCE.read_text()
modules_block = re.search(r'track_d_audit_modules=\(\n(.*?)\n\)', source, re.S)
assert modules_block, 'No audit module manifest'
modules = modules_block.group(1).split()
assert len(modules) == len(set(modules)) == 9

with tempfile.TemporaryDirectory() as td:
    root = Path(td) / 'repo'
    root.mkdir()
    scripts = root / 'scripts'
    scripts.mkdir()
    shutil.copy2(SOURCE, scripts / 'verify_track_d_locally.sh')
    (root / 'lean-toolchain').write_text('fake toolchain\n')
    (root / 'lakefile.toml').write_text('name = "fake"\n')
    (scripts / 'audit_all_axioms_local.sh').write_text('#!/bin/bash\necho global-audit >> "$MOCK_LAKE_LOG"\n')
    for name in re.findall(r'python3(?: -O)? scripts/([\w.-]+\.py)', source):
        path = scripts / name
        if name == 'check_banana_actual_coordinate_functor.py':
            path.write_text('import sys\nif "--probe-guard" in sys.argv:\n print("CHECK_GUARD_ACTIVE")\n sys.exit(1)\n')
        else:
            path.write_text('pass\n')
    # Only the axiom-report parser needs to know how fake Lake wrote output.
    (scripts / 'check_axiom_report.py').write_text('import sys\nsys.exit(0 if "fake-axioms-allowed" in open(sys.argv[2]).read() else 1)\n')
    for name in modules:
        (root/'BANANA'/'NonPrecompact').mkdir(parents=True,exist_ok=True)
        (root/'BANANA'/'NonPrecompact'/f'{name}.lean').write_text('#print axioms fake\n')
    (root/'BANANA.lean').write_text('-- fake Lean root\n')
    subprocess.run(['git','init','-q'],cwd=root,check=True)
    subprocess.run(['git','config','user.email','audit@example.invalid'],cwd=root,check=True)
    subprocess.run(['git','config','user.name','Audit Test'],cwd=root,check=True)
    subprocess.run(['git','add','.'],cwd=root,check=True)
    subprocess.run(['git','commit','-q','-m','mock checkout'],cwd=root,check=True)
    sha = subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
    bindir=Path(td)/'bin';bindir.mkdir()
    fake = bindir/'lake'
    fake.write_text('#!/bin/bash\necho "$*" >> "$MOCK_LAKE_LOG"\nif [[ "$1" == env ]]; then\n echo fake-axioms-allowed\nfi\n')
    fake.chmod(0o755)
    env=os.environ.copy()
    env['PATH']=str(bindir)+os.pathsep+env['PATH']
    env['EXPECTED_HEAD_SHA']=sha
    log=Path(td)/'lake.log'
    env['MOCK_LAKE_LOG']=str(log)
    result=subprocess.run(['bash','scripts/verify_track_d_locally.sh'],cwd=root,env=env,capture_output=True,text=True)
    if result.returncode:
        raise AssertionError(f'Local gate fake-Lake run exited {result.returncode}:\n{result.stdout}\n{result.stderr}')
    lines=log.read_text().splitlines()
    for module in modules:
        assert lines.count(f'build +BANANA.NonPrecompact.{module}') == 1, (module,lines)
        assert lines.count(f'env lean BANANA/NonPrecompact/{module}.lean') == 1, (module,lines)
    assert lines.count('build BANANA')==1
    assert lines.count('global-audit')==1
    bad=env.copy();bad['EXPECTED_HEAD_SHA']='0'*40
    result2=subprocess.run(['bash','scripts/verify_track_d_locally.sh'],cwd=root,env=bad,capture_output=True,text=True)
    assert result2.returncode==2 and 'Wrong checkout SHA' in result2.stderr
    print('PASS: exact committed local driver syntax and fake-Lake orchestration')
    print(f'PASS: all {len(modules)} distinct audit modules built and checked')
    print('PASS: root build, global axiom audit, negative guard, SHA rejection')
    print('LIMIT: fake Lake and fake Lean outputs; this is NOT kernel verification')

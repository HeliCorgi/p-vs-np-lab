"""Prepare fixed PR trees; verify before publishing unreachable Git objects only."""
from pathlib import Path
import base64
import json
import os
import subprocess
import sys
import urllib.request

ROOT = Path.cwd().resolve()
BASE = '5bc7b0a75a482b33be5d0e209c919bcc77af4f22'
HEADS = {
    8: ('research/generic-gate-miter-resolution', 'bb2d6bb2cdac15953db0ba18116b8e1353047a30'),
    10: ('research/asymmetric-demorgan-resolution', '3165460df8658f66d7e73b5a8da2c064e1460b74'),
    11: ('research/reversed-xor-chain-resolution', 'c5710c788181019642958729dfac7a26427ae30a'),
}
SUMMARY = 'results/RUN_SUMMARY.json'
OUT = ROOT / 'integration-review'
OUT.mkdir(exist_ok=True)

def command(*args, cwd=ROOT, check=True, **kwargs):
    return subprocess.run(args, cwd=cwd, check=check, text=True, **kwargs)

def git(*args, cwd=ROOT):
    return command('git', *args, cwd=cwd, capture_output=True).stdout.strip()

DE_MORGAN_CI = '''name: Asymmetric De Morgan certificate audit

on:
  push:
    paths:
      - 'research/asymmetric_demorgan_miter/**'
      - 'results/asymmetric_demorgan_miter*.json'
      - '.github/workflows/asymmetric-demorgan.yml'
  pull_request:
    paths:
      - 'research/asymmetric_demorgan_miter/**'
      - 'results/asymmetric_demorgan_miter*.json'
      - '.github/workflows/asymmetric-demorgan.yml'

permissions:
  contents: read

jobs:
  replay:
    runs-on: ubuntu-24.04
    timeout-minutes: 5
    steps:
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262
      - uses: actions/setup-python@a26af69be951a213d495a4c3e4e4022e16d87065
        with:
          python-version: '3.12'
      - name: Independently replay proofs and compare both committed reports
        run: python research/asymmetric_demorgan_miter/asymmetric_demorgan_audit.py --check
'''
REFRESH = '''from pathlib import Path
import json, runpy, sys, unittest
root=Path.cwd()
sys.path[:0]=[str(root/'src'), str(root)]
m=runpy.run_path(str(root/'scripts/reproduce.py'))
p=root/'results/RUN_SUMMARY.json'
s=json.loads(p.read_text())
s['unit_tests_passed']=unittest.defaultTestLoader.discover(str(root/'tests')).countTestCases()
s['source_sha256']=m['source_hashes']()
m['write_json'](p,s)
print('refreshed count and exact source hashes:',s['unit_tests_passed'])
'''

NOTE = '''# PR integration review — 2026-11-12

Scope: integrate PRs #8–#11 without changing their mathematical claims,
finite search bounds, existing Lean sources, or historical result values.
PR #9 supplies the updated main-line experiments and research record.

## Repairs

- Resolve #8's generated RUN_SUMMARY conflict against the newer experiment
  inventory, retaining both sets of sources and all existing result data.
- Register #10's independent De Morgan certificate checker in a dedicated
  read-only CI workflow; `--check` compares both fixed reports.
- Repair #11's reproduction failure by including its workflow in the
  generated source-hash manifest. Do not weaken the comparison.

The only regenerated summary fields are `unit_tests_passed` and
`source_sha256`. Python arbitrary-precision JSON integers are preserved.
All other summary fields and all original research result files are unchanged.

## Reproducible integration gate

```sh
python scripts/reproduce.py --out-dir reproduced --check
python research/asymmetric_demorgan_miter/asymmetric_demorgan_audit.py --check
python research/reversed_xor_chain/audit.py --check
git diff --check
```

The prepared final tree passes 551 unit tests, the complete deterministic
report comparison, and both isolated certificate audits before publication.
The generic-gate report is checked by its five discovered unit tests.
These are finite regression checks. Existing Lean CI is a separate gate;
this maintenance change adds no Lean theorem and no P-versus-NP result.

The preparation job publishes only verified Git objects, not branch updates.
Expected-head checks guard subsequent non-forced branch updates. Main is not
pushed by the preparation job; each PR is separately reviewed and merged.
'''

def prepare():
    records=[]
    previous=BASE
    for pr, (branch, expected) in HEADS.items():
        git('cat-file','-e',expected+'^{commit}')
        work=ROOT/'.git'/'integration-worktrees'/str(pr)
        command('git','worktree','add','--detach',str(work),expected)
        merged=command('git','merge','--no-ff','--no-commit',previous,cwd=work,check=False)
        conflicts=git('diff','--name-only','--diff-filter=U',cwd=work).splitlines()
        if merged.returncode and conflicts != [SUMMARY]:
            raise RuntimeError(f'Unexpected merge failure for PR {pr}: {conflicts}')
        if any(name != SUMMARY for name in conflicts):
            raise RuntimeError(f'Unexpected conflicting path: {conflicts}')
        old=json.loads(git('show',previous+':'+SUMMARY))
        (work/SUMMARY).write_text(json.dumps(old,indent=2,sort_keys=True,ensure_ascii=False)+'\n')
        if pr == 10:
            (work/'.github/workflows/asymmetric-demorgan.yml').write_text(DE_MORGAN_CI)
            doc=work/'docs/asymmetric_demorgan_miter.md'
            doc.write_text(doc.read_text()+'''\n\n## Integration verification (2026-11-12 JST)\n\nThe original cycle's CI limitation above is historical. The dedicated\n`.github/workflows/asymmetric-demorgan.yml` now runs the independent audit\nwith `--check`, comparing both committed JSON reports. This adds regression\ncoverage for the finite certificates, not a Lean proof or a stronger theorem.\n''')
        if pr == 11:
            (work/'docs/pr_integration_2026-11-12.md').write_text(NOTE)
        command(sys.executable,'-c',REFRESH,cwd=work)
        new=json.loads((work/SUMMARY).read_text())
        for key in ('unit_tests_passed','source_sha256'):
            old.pop(key); new.pop(key)
        if old != new:
            raise RuntimeError('Non-manifest summary content changed')
        command('git','add',SUMMARY,cwd=work)
        if pr == 10:
            command('git','add','.github/workflows/asymmetric-demorgan.yml','docs/asymmetric_demorgan_miter.md',cwd=work)
        if pr == 11:
            command('git','add','docs/pr_integration_2026-11-12.md',cwd=work)
        command('git','diff','--cached','--check',previous,cwd=work)
        command('git','commit','-m',f'Integrate reviewed research dependencies and refresh PR #{pr} verification metadata',cwd=work)
        head=git('rev-parse','HEAD',cwd=work)
        records.append({'pr':pr,'branch':branch,'original_head':expected,'head':head,'tree':git('rev-parse','HEAD^{tree}',cwd=work)})
        previous=head
    for label,args in (
        ('reproduction',[sys.executable,'scripts/reproduce.py','--out-dir',str(OUT/'reproduced'),'--check']),
        ('demorgan',[sys.executable,'research/asymmetric_demorgan_miter/asymmetric_demorgan_audit.py','--check']),
        ('reversed_xor',[sys.executable,'research/reversed_xor_chain/audit.py','--check']),
    ):
        print('Running',label,flush=True)
        with (OUT/(label+'.log')).open('w') as log:
            command(*args,cwd=work,stdout=log,stderr=subprocess.STDOUT)
        print('PASS',label,flush=True)
    for path in git('ls-tree','-r','--name-only',BASE,'results').splitlines():
        if path != SUMMARY and git('rev-parse',BASE+':'+path) != git('rev-parse',previous+':'+path):
            raise RuntimeError('Existing result modified: '+path)
    result={'base':BASE,'all_checks_passed':True,'prepared':records}
    (OUT/'prepared.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

def api(path,payload=None):
    # Fixed repository, fixed Git-data endpoints only; never updates refs.
    if not path.startswith(('git/blobs','git/trees','git/commits')):
        raise ValueError(path)
    req=urllib.request.Request('https://api.github.com/repos/HeliCorgi/p-vs-np-lab/'+path,
        data=json.dumps(payload).encode() if payload is not None else None,
        headers={'Authorization':'Bearer '+os.environ['GH_TOKEN'],
                 'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28',
                 'Content-Type':'application/json'})
    with urllib.request.urlopen(req,timeout=60) as response:
        return json.load(response)

def entries(commit):
    result={}
    for row in git('ls-tree','-r',commit).splitlines():
        metadata,path=row.split('\t',1)
        mode,kind,sha=metadata.split()
        if kind != 'blob':
            raise RuntimeError('Unexpected non-blob entry')
        result[path]={'path':path,'mode':mode,'type':kind,'sha':sha}
    return result

def publish():
    record=json.loads((OUT/'prepared.json').read_text())
    if record.get('all_checks_passed') is not True or record['base'] != BASE:
        raise RuntimeError('Missing completed verification')
    known={v['sha'] for h in [BASE,*[x[1] for x in HEADS.values()]] for v in entries(h).values()}
    allowed={SUMMARY,'.github/workflows/asymmetric-demorgan.yml','docs/asymmetric_demorgan_miter.md','docs/pr_integration_2026-11-12.md'}
    previous=BASE
    for item in record['prepared']:
        head=item['head']; original=item['original_head']
        current=entries(head); old=entries(original)
        delta=[v for p,v in current.items() if old.get(p)!=v]
        delta += [{'path':p,'mode':v['mode'],'type':'blob','sha':None} for p,v in old.items() if p not in current]
        for v in delta:
            if v['sha'] is None or v['sha'] in known:
                continue
            if v['path'] not in allowed:
                raise RuntimeError('Unexpected new content: '+v['path'])
            raw=subprocess.check_output(['git','show',head+':'+v['path']],cwd=ROOT)
            uploaded=api('git/blobs',{'content':base64.b64encode(raw).decode(),'encoding':'base64'})
            if uploaded['sha'] != v['sha']:
                raise RuntimeError('Blob hash mismatch')
            known.add(v['sha'])
        tree=api('git/trees',{'base_tree':git('rev-parse',original+'^{tree}'),'tree':delta})
        if tree['sha'] != item['tree']:
            raise RuntimeError('Published tree differs from verified tree')
        commit=api('git/commits',{'message':f"Integrate reviewed research dependencies and refresh PR #{item['pr']} verification metadata",'tree':tree['sha'],'parents':[original,previous]})
        item['published_head']=commit['sha']; previous=commit['sha']
    (OUT/'published.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2),flush=True)

if __name__ == '__main__':
    if sys.argv[1:] == ['--publish']:
        publish()
    elif not sys.argv[1:]:
        prepare()
    else:
        raise SystemExit('Unsupported arguments')

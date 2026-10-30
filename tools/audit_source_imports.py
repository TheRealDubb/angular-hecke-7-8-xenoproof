"""Compare the entire source index with Lean's own header parser, not a regex."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, time
from rebuild_from_source import check_plan, save, sha

def audit(root, dest, lean):
    root=Path(root).resolve();dest=Path(dest).resolve();lean=Path(lean).resolve()
    dest.mkdir(parents=True,exist_ok=True)
    index=json.loads((root/'metadata/MODULE_INDEX.json').read_text())
    check_plan(root,index)
    rows=dest/'source_import_inputs.tsv'
    rows.write_text(''.join(n+'\t'+str(root/index['modules'][n]['path'])+'\n' for n in index['build_order']),encoding='utf-8')
    harness=root/'tools/ParseSourceImports.lean';log=dest/'source_import_parser.log'
    cmd=[str(lean),'--run',str(harness),str(rows)]
    env=os.environ.copy();env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
    t=time.monotonic()
    with log.open('wb') as f:r=subprocess.run(cmd,cwd=root/'tools',env=env,stdout=f,stderr=subprocess.STDOUT)
    result={'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-t,
      'harness_sha256':sha(harness),'lean_sha256':sha(lean),'index_sha256':sha(root/'metadata/MODULE_INDEX.json'),
      'log_sha256':sha(log),'passed':False}
    if r.returncode:
        save(dest/'SOURCE_IMPORT_AUDIT.json',result)
        raise ValueError('Lean header parser failed; inspect '+str(log))
    actual={}
    for line in log.read_text(encoding='utf-8').splitlines():
        rec=json.loads(line);assert rec['module'] not in actual
        actual[rec['module']]=rec['imports']
    assert set(actual)==set(index['modules'])
    mismatches={n:{'source':actual[n],'index':rec['imports']} for n,rec in index['modules'].items()
      if list(dict.fromkeys(actual[n]))!=list(dict.fromkeys(rec['imports']))}
    result.update(source_modules=len(actual),mismatches=mismatches,passed=not mismatches,
      scope='Explicit source imports parsed by pinned Lean. Duplicate module imports compared in first-occurrence order; implicit Init remains a toolchain dependency.')
    save(dest/'SOURCE_IMPORT_AUDIT.json',result)
    if mismatches:raise ValueError('Source/index import mismatch: '+str(list(mismatches)))
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    p.add_argument('--build-dir',type=Path,required=True);p.add_argument('--lean',required=True)
    a=p.parse_args();print(json.dumps(audit(a.root,a.build_dir,a.lean),indent=2))

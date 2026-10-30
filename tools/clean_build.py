"""Dependency-scheduled clean build. No author cache, downloads, or theorem edits.

Run from any directory with --lean PATH --build-dir NEW_DIRECTORY.
Resumption accepts only this build's matching source/dependency/output hashes.
The sequential original helper is retained as a separate historical recipe.
"""
from pathlib import Path
import argparse, concurrent.futures, datetime, hashlib, json, os, shutil, subprocess, time
from rebuild_from_source import check_plan, sha, save

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    p.add_argument('--lean',required=True)
    p.add_argument('--build-dir',type=Path,required=True)
    p.add_argument('--jobs',type=int,default=2)
    a=p.parse_args()
    if a.jobs<1:raise ValueError('--jobs must be positive')
    root=a.root.resolve(); dest=a.build_dir.resolve()
    index=json.loads((root/'metadata/MODULE_INDEX.json').read_text(encoding='utf-8'))
    print(json.dumps(check_plan(root,index)),flush=True)
    pins=json.loads((root/'metadata/DEPENDENCY_PINS.json').read_text())
    lean=Path(shutil.which(a.lean) or a.lean).resolve()
    if subprocess.check_output([lean,'--short-version'],text=True).strip()!=pins['lean']['version']:
        raise ValueError('Wrong Lean version')
    rev=subprocess.check_output([lean,'--githash'],text=True).strip()
    if rev!=pins['lean']['revision']:raise ValueError('Wrong Lean revision')
    if dest==root or dest.is_relative_to(root/'lean'):raise ValueError('Separate build directory required')
    identity={'source_root':str(root),'index_sha256':sha(root/'metadata/MODULE_INDEX.json'),
      'lean_sha256':sha(lean),'revision':rev,'recipe_sha256':sha(Path(__file__)),
      'helper_sha256':sha(Path(__file__).with_name('rebuild_from_source.py'))}
    if dest.exists():
        if not (dest/'BUILD_IDENTITY.json').exists() or json.loads((dest/'BUILD_IDENTITY.json').read_text())!=identity:
            raise ValueError('Existing directory has a different build identity')
    else:save(dest/'BUILD_IDENTITY.json',identity)
    objects=dest/'objects';objects.mkdir(exist_ok=True)
    env=os.environ.copy();env['LEAN_PATH']=str(objects);env['LEAN_SRC_PATH']=str(root/'lean')
    # No --setup/importArts/plugins from the author's records are admitted.
    completed={}; pending=list(index['build_order']); running={}; failed=[]; newly=0
    start=time.monotonic()
    def compile_one(name,dependencies):
        rec=index['modules'][name];stem=Path(*name.split('.'))
        obj=objects/stem.with_suffix('.olean');log=dest/'logs'/stem.with_suffix('.log')
        receipt=dest/'receipts'/stem.with_suffix('.json')
        inputs={'source_sha256':rec['sha256'],'dependencies':dependencies,'identity':identity}
        if receipt.exists():
            prior=json.loads(receipt.read_text());out=prior.get('artifacts',{})
            if prior.get('exit_code')==0 and prior.get('inputs')==inputs and out and all(
              (dest/f).is_file() and sha(dest/f)==h for f,h in out.items()):
                return name,prior,False
        obj.parent.mkdir(parents=True,exist_ok=True);log.parent.mkdir(parents=True,exist_ok=True)
        opts=[]
        if rec['provider'] in {'OAI-003','angular development','mathlib'}:opts+=['-DautoImplicit=false']
        if rec['provider']=='mathlib':opts+=['-DmaxSynthPendingDepth=3','-Dpp.unicode.fun=true']
        cmd=[str(lean),'-j1','-R',str(root/'lean'),*opts,'-o',str(obj),str(root/rec['path'])]
        t=time.monotonic()
        with log.open('wb') as f:r=subprocess.run(cmd,cwd=root/'lean',env=env,stdout=f,stderr=subprocess.STDOUT)
        paths=[obj,obj.with_suffix('.olean.private'),obj.with_suffix('.olean.server'),obj.with_suffix('.ir')]
        out={q.relative_to(dest).as_posix():sha(q) for q in paths if q.is_file()}
        record={'module':name,'command':cmd,'inputs':inputs,'exit_code':r.returncode,
          'seconds':time.monotonic()-t,'artifacts':out,'log_sha256':sha(log),
          'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'independent_kernel_replay_performed':False}
        if not obj.exists() and r.returncode==0:record['exit_code']=1;record['error']='Missing output'
        save(receipt,record)
        return name,record,True
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        while pending or running:
            if not failed:
                for name in list(pending):
                    if len(running)>=a.jobs:break
                    # The large analytic source files are compiled one at a time.
                    heavy=index['modules'][name]['provider'] in {'OAI-003','angular development'}
                    if heavy and running:continue
                    if any(index['modules'][n]['provider'] in {'OAI-003','angular development'} for n in running.values()):break
                    deps=[d for d in index['modules'][name]['imports'] if d in index['modules']]
                    if not all(d in completed for d in deps):continue
                    pending.remove(name)
                    f=pool.submit(compile_one,name,{d:completed[d] for d in deps})
                    running[f]=name
                    if heavy:break
            if not running:
                if failed:break
                raise ValueError('Dependency scheduling stalled')
            ready,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
            for f in ready:
                running.pop(f);name,rec,isnew=f.result();newly+=isnew
                if rec['exit_code']!=0:failed.append(name)
                else:completed[name]=hashlib.sha256(json.dumps(rec['artifacts'],sort_keys=True).encode()).hexdigest()
                progress={'module':name,'exit_code':rec['exit_code'],'seconds':round(rec['seconds'],2),
                  'completed':len(completed),'total':len(index['modules']),'running':list(running.values()),
                  'new_compilation':isnew,'elapsed_seconds':round(time.monotonic()-start,2)}
                print(json.dumps(progress),flush=True);save(dest/'PROGRESS.json',progress)
    result={'all_roots_compiled':not failed and not pending,'roots':index['roots'],'failed_modules':failed,
      'completed_source_modules':len(completed),'new_compilations':newly,'identity':identity,
      'elapsed_seconds':time.monotonic()-start,'independent_kernel_replay_performed':False}
    save(dest/'BUILD_RESULT.json',result);print(json.dumps(result),flush=True)
    return 0 if result['all_roots_compiled'] else 1

if __name__=='__main__':raise SystemExit(main())

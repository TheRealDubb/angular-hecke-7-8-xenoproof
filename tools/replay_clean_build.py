"""Hash-check a successful clean build, then replay both public roots together."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, subprocess, time
from rebuild_from_source import check_plan, save, sha
from audit_source_imports import audit

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    p.add_argument('--build-dir',type=Path,required=True)
    p.add_argument('--lean',required=True)
    p.add_argument('--checker',required=True)
    a=p.parse_args();root=a.root.resolve();dest=a.build_dir.resolve()
    lean=Path(a.lean).resolve();checker=Path(a.checker).resolve()
    index=json.loads((root/'metadata/MODULE_INDEX.json').read_text(encoding='utf-8'))
    print(json.dumps(check_plan(root,index)),flush=True)
    print(json.dumps(audit(root,dest,lean)),flush=True)
    result=json.loads((dest/'BUILD_RESULT.json').read_text());identity=result['identity']
    if not result['all_roots_compiled'] or result['completed_source_modules']!=len(index['modules']):
        raise ValueError('Full successful clean build required')
    if identity['index_sha256']!=sha(root/'metadata/MODULE_INDEX.json') or identity['lean_sha256']!=sha(lean):
        raise ValueError('Source index or compiler changed')
    fingerprints={};files=0;reused=0
    for name in index['build_order']:
        rec=json.loads((dest/'receipts'/Path(*name.split('.')).with_suffix('.json')).read_text())
        inputs=rec['inputs'];deps={d:fingerprints[d] for d in index['modules'][name]['imports'] if d in fingerprints}
        if rec['exit_code']!=0 or inputs!={'source_sha256':index['modules'][name]['sha256'],'dependencies':deps,'identity':identity}:
            raise ValueError('Receipt inputs mismatch: '+name)
        if rec.get('record_kind')=='verified_same_source_checkpoint_reuse':
            reused+=1
            origin=(root/rec['checkpoint_reuse']['original_receipt']).resolve()
            if not origin.is_relative_to(root/'evidence/independent_repair/failed_import_removal_attempt'):
                raise ValueError('Checkpoint receipt escapes preserved attempt')
            if sha(origin)!=rec['checkpoint_reuse']['original_receipt_sha256']:
                raise ValueError('Original compilation receipt changed: '+name)
            prior=json.loads(origin.read_text())
            if rec['compilation_inputs']!=prior['inputs']:
                raise ValueError('Original compilation inputs mismatch: '+name)
            if prior['inputs']['source_sha256']!=inputs['source_sha256'] or prior['inputs']['dependencies']!=deps:
                raise ValueError('Checkpoint source/dependencies changed: '+name)
            oldid=dict(prior['inputs']['identity']);newid=dict(identity)
            oldid.pop('index_sha256');newid.pop('index_sha256')
            if oldid!=newid:raise ValueError('Checkpoint toolchain or recipe changed: '+name)
            for key in ['command','artifacts','log_sha256','exit_code','timestamp_utc','seconds']:
                if rec[key]!=prior[key]:raise ValueError('Compilation record changed: '+name+' '+key)
        if not rec['artifacts']:raise ValueError('Missing artifacts: '+name)
        for f,h in rec['artifacts'].items():
            if sha(dest/f)!=h:raise ValueError('Artifact hash mismatch: '+f)
            files+=1
        log=dest/'logs'/Path(*name.split('.')).with_suffix('.log')
        if sha(log)!=rec['log_sha256']:raise ValueError('Log hash mismatch: '+name)
        fingerprints[name]=hashlib.sha256(json.dumps(rec['artifacts'],sort_keys=True).encode()).hexdigest()
    save(dest/'PRE_REPLAY_INTEGRITY.json',{'source_modules':len(fingerprints),'artifact_parts':files,
      'verified_checkpoint_reuses':reused,'source_import_headers_verified':True,'passed':True})
    objects=dest/'objects';env=os.environ.copy();env['LEAN_PATH']=str(objects);env['LEAN_SRC_PATH']=str(root/'lean')
    source=root/'tools/ReplayRoots.lean'
    cmd=[str(lean),'-j1','-R',str(root/'tools'),'-o',str(objects/'ReplayRoots.olean'),str(source)]
    with (dest/'replay_harness_compile.log').open('wb') as f:
        c=subprocess.run(cmd,cwd=root/'tools',env=env,stdout=f,stderr=subprocess.STDOUT)
    save(dest/'REPLAY_HARNESS.json',{'command':cmd,'exit_code':c.returncode,'source_sha256':sha(source),
      'log_sha256':sha(dest/'replay_harness_compile.log'),'object_sha256':sha(objects/'ReplayRoots.olean') if c.returncode==0 else None})
    if c.returncode:return c.returncode
    command=[str(checker),'--fresh','--verbose','ReplayRoots']
    record={'command':command,'LEAN_PATH':str(objects),'checker_sha256':sha(checker),
      'roots':index['roots'],'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'status':'running','scope':'Native Lean fresh-environment replay of both public roots and their full imported environment, using only this clean build plus the pinned toolchain. Not an external kernel implementation.'}
    t=time.monotonic()
    with (dest/'kernel_replay.log').open('wb') as f:
        process=subprocess.Popen(command,cwd=root/'tools',env=env,stdout=f,stderr=subprocess.STDOUT)
        record['pid']=process.pid;save(dest/'KERNEL_REPLAY.json',record);print(json.dumps(record),flush=True)
        code=process.wait()
    record.update(status='completed',exit_code=code,elapsed_seconds=time.monotonic()-t,
      end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),log_sha256=sha(dest/'kernel_replay.log'))
    save(dest/'KERNEL_REPLAY.json',record);print(json.dumps(record),flush=True)
    if code:return code
    checks=[]
    for name,arguments in [('PublicClosureCensus',['--run']),('StandardAxiomTypes',[])]:
        harness=root/f'tools/{name}.lean';checkcmd=[str(lean),*arguments,str(harness)]
        log=dest/f'{name}.log';began=time.monotonic()
        with log.open('wb') as f:
            checked=subprocess.run(checkcmd,cwd=root/'tools',env=env,stdout=f,stderr=subprocess.STDOUT)
        evidence={'check':name,'command':checkcmd,'exit_code':checked.returncode,
          'source_sha256':sha(harness),'log_sha256':sha(log),'seconds':time.monotonic()-began}
        checks.append(evidence);save(dest/f'{name}.json',evidence);print(json.dumps(evidence),flush=True)
        if checked.returncode:return checked.returncode
    save(dest/'VERIFICATION_RESULT.json',{'full_clean_build':True,'fresh_kernel_replay':True,'source_import_audit':True,
      'public_proof_census':True,'standard_axiom_types':True,'roots':index['roots'],
      'source_modules':len(index['modules']),'replay_recipe_sha256':sha(Path(__file__)),
      'evidence_scope':'Freshly built source closure and native Lean kernel replay; external toolchain remains trusted.'})
    return 0

if __name__=='__main__':raise SystemExit(main())

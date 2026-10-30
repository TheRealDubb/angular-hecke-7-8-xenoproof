"""Verify the repository payload and optional original release assets; no Lean work."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, sys
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--assets',type=Path);a=ap.parse_args()
    root=Path(__file__).resolve().parent
    records=json.loads((root/'MANIFEST_SHA256.json').read_text(encoding='utf8'))['files']
    errors=[];seen=set()
    for r in records:
        n=r['path'];q=PurePosixPath(n);p=root/n
        if n in seen or q.is_absolute() or '..' in q.parts or ':' in n or '\\' in n:
            errors.append('Unsafe or duplicate path: '+n);continue
        seen.add(n)
        if p.is_symlink() or not p.resolve().is_relative_to(root) or not p.is_file():errors.append('Missing or unsafe: '+n)
        elif p.stat().st_size!=r['bytes'] or sha(p)!=r['sha256']:errors.append('Mismatch: '+n)
    actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()
            and not any(s in {'.git','__pycache__','.review-build'} for s in p.relative_to(root).parts)}
    errors.extend('Unexpected: '+n for n in sorted(actual-seen-{'MANIFEST_SHA256.json'}))
    if a.assets:
        for r in json.loads((root/'RELEASE_ASSETS.json').read_text())['assets']:
            p=a.assets/r['name']
            if not p.is_file() or p.stat().st_size!=r['bytes'] or sha(p)!=r['sha256']:errors.append('Asset mismatch: '+r['name'])
    print(json.dumps({'passed':not errors,'payload_files':len(records),'assets_checked':bool(a.assets),'errors':errors,'new_lean_verification':False},indent=2))
    return bool(errors)
if __name__=='__main__':sys.exit(main())

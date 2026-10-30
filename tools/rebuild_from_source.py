"""Inspect the source build plan; compile only with explicit --run. No downloads."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')


def check_plan(root, index):
    modules = index['modules']
    order = index['build_order']
    if len(set(order)) != len(order) or set(order) != set(modules):
        raise ValueError('Build order does not enumerate each module exactly once')
    seen = set()
    external = set(index['toolchain_modules'])
    for name in order:
        rec = modules[name]
        path = (root / rec['path']).resolve()
        if not path.is_relative_to(root / 'lean'):
            raise ValueError('Source escapes the Lean tree: ' + name)
        if sha(path) != rec['sha256']:
            raise ValueError('Source SHA-256 mismatch: ' + name)
        for dep in rec['imports']:
            if dep not in seen and dep not in external:
                raise ValueError('Import absent or out of order: ' + name + ' -> ' + dep)
        seen.add(name)
    for rec in index['resources']:
        path = (root / rec['path']).resolve()
        if not path.is_relative_to(root) or sha(path) != rec['sha256']:
            raise ValueError('Elaboration resource mismatch: ' + rec['path'])
    if any(n not in seen for n in index['roots']):
        raise ValueError('Missing public root')
    return dict(source_modules=len(order), toolchain_imports=len(external),
                resources=len(index['resources']), roots=index['roots'],
                plan_passed=True, new_compilation_performed=False,
                independent_kernel_replay_performed=False)


def build(root, index, args, pins):
    lean = shutil.which(args.lean)
    if not lean:
        raise ValueError('Lean executable not found: ' + args.lean)
    lean = str(Path(lean).resolve())
    version = subprocess.check_output([lean, '--short-version'], text=True).strip()
    revision = subprocess.check_output([lean, '--githash'], text=True).strip()
    if version != pins['lean']['version'] or revision != pins['lean']['revision']:
        raise ValueError('Lean version/revision does not match the pinned toolchain')
    build_dir = (args.build_dir or root / '.review-build').resolve()
    if build_dir == root or build_dir.is_relative_to(root / 'lean'):
        raise ValueError('Choose a separate build directory')
    if build_dir.exists() and not (build_dir / 'BUILD_IDENTITY.json').exists():
        raise ValueError('Existing directory is not this helper\'s build directory')
    identity = dict(index_sha256=sha(root / 'metadata/MODULE_INDEX.json'),
                    executable_sha256=sha(Path(lean)), revision=revision,
                    recipe_sha256=sha(Path(__file__)), source_root=str(root))
    identity_path = build_dir / 'BUILD_IDENTITY.json'
    if identity_path.exists():
        if json.loads(identity_path.read_text()) != identity:
            raise ValueError('Build identity changed; choose a new --build-dir')
    else:
        save(identity_path, identity)
    objects = build_dir / 'objects'
    objects.mkdir(exist_ok=True)
    env = os.environ.copy()
    # Do not admit the author's cached imports via an inherited LEAN_PATH.
    env['LEAN_PATH'] = str(objects)
    env['LEAN_SRC_PATH'] = str(root / 'lean')
    fingerprints = {}
    new_count = 0
    for number, name in enumerate(index['build_order'], 1):
        rec = index['modules'][name]
        source = root / rec['path']
        stem = Path(*name.split('.'))
        obj = objects / stem.with_suffix('.olean')
        receipt = build_dir / 'receipts' / stem.with_suffix('.json')
        log = build_dir / 'logs' / stem.with_suffix('.log')
        dependencies = {d: fingerprints[d] for d in rec['imports'] if d in fingerprints}
        # Toolchain, recipe, package source hashes, and direct dependency artifacts
        # jointly anchor resumption. This is not a proof-object checker.
        inputs = dict(source_sha256=rec['sha256'], dependencies=dependencies,
                      identity=identity)
        prior = json.loads(receipt.read_text()) if receipt.exists() else None
        artifacts = [obj, obj.with_suffix('.olean.private'), obj.with_suffix('.olean.server'),
                     obj.with_suffix('.ir')]
        if prior and prior.get('exit_code') == 0 and prior.get('inputs') == inputs:
            expected = prior.get('artifacts', {})
            if expected and all((build_dir / p).is_file() and sha(build_dir / p) == h
                                for p, h in expected.items()):
                fingerprints[name] = hashlib.sha256(json.dumps(expected, sort_keys=True).encode()).hexdigest()
                continue
        if args.max_modules is not None and new_count >= args.max_modules:
            print(json.dumps(dict(stopped_at_limit=True, newly_compiled=new_count,
                                  next_module=name, all_roots_compiled=False)))
            return 0
        obj.parent.mkdir(parents=True, exist_ok=True)
        log.parent.mkdir(parents=True, exist_ok=True)
        options = []
        if rec['provider'] in {'OAI-003', 'angular development', 'mathlib'}:
            options.append('-DautoImplicit=false')
        if rec['provider'] == 'mathlib':
            options += ['-DmaxSynthPendingDepth=3', '-Dpp.unicode.fun=true']
        cmd = [lean, '-j1', '-R', str(root / 'lean'), *options, '-o', str(obj), str(source)]
        start = time.monotonic()
        with log.open('wb') as f:
            result = subprocess.run(cmd, cwd=root / 'lean', env=env, stdout=f, stderr=subprocess.STDOUT)
        outputs = {p.relative_to(build_dir).as_posix(): sha(p) for p in artifacts if p.is_file()}
        record = dict(module=name, command=cmd, inputs=inputs, exit_code=result.returncode,
                      seconds=time.monotonic() - start, artifacts=outputs, log_sha256=sha(log),
                      timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      independent_kernel_replay_performed=False)
        if result.returncode == 0 and not obj.exists():
            record['exit_code'] = 1
            record['error'] = 'Compiler returned success without the requested object'
        save(receipt, record)
        print(json.dumps(dict(module=name, position=number, exit_code=record['exit_code'],
                              seconds=round(record['seconds'], 2))), flush=True)
        if record['exit_code'] != 0:
            return 1
        fingerprints[name] = hashlib.sha256(json.dumps(outputs, sort_keys=True).encode()).hexdigest()
        new_count += 1
    save(build_dir / 'BUILD_RESULT.json', dict(all_roots_compiled=True,
         roots=index['roots'], new_compilations=new_count, identity=identity,
         independent_kernel_replay_performed=False))
    print(json.dumps(dict(all_roots_compiled=True, new_compilations=new_count,
                          independent_kernel_replay_performed=False)))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--plan', action='store_true')
    group.add_argument('--run', action='store_true')
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--build-dir', type=Path)
    parser.add_argument('--max-modules', type=int)
    args = parser.parse_args()
    try:
        if args.max_modules is not None and args.max_modules < 0:
            raise ValueError('--max-modules must be nonnegative')
        root = args.root.resolve()
        index = json.loads((root / 'metadata/MODULE_INDEX.json').read_text(encoding='utf-8'))
        print(json.dumps(check_plan(root, index)), flush=True)
        if args.run:
            pins = json.loads((root / 'metadata/DEPENDENCY_PINS.json').read_text(encoding='utf-8'))
            return build(root, index, args, pins)
        return 0
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as e:
        print(json.dumps(dict(error=str(e))), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())

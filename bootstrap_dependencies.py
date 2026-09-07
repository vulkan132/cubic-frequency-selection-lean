"""Retrieve official source archives at exactly the upstream pinned revisions."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parent
VENDOR = ROOT / 'vendor'
MATHLIB = VENDOR / 'mathlib4-4.33.0'
if not (MATHLIB / 'lake-manifest.json').exists():
    VENDOR.mkdir(exist_ok=True)
    archive = ROOT / 'mathlib-v4.33.0.zip'
    if not archive.exists():
        url = 'https://codeload.github.com/leanprover-community/mathlib4/zip/refs/tags/v4.33.0'
        with urllib.request.urlopen(url, timeout=180) as response:
            archive.write_bytes(response.read())
    with zipfile.ZipFile(archive) as z:
        for member in z.infolist():
            target = (VENDOR / member.filename).resolve()
            if not target.is_relative_to(VENDOR.resolve()):
                raise ValueError('Mathlib archive traversal')
        z.extractall(VENDOR)
manifest = json.loads((MATHLIB / 'lake-manifest.json').read_text())

def retrieve(pkg):
    name, rev = pkg['name'], pkg['rev']
    repo = pkg['url'].removeprefix('https://github.com/').removesuffix('.git')
    url = f'https://codeload.github.com/{repo}/zip/{rev}'
    archive = VENDOR / f'{name}-{rev}.zip'
    target = (VENDOR / name).resolve()
    if not target.is_relative_to(VENDOR.resolve()):
        raise ValueError('Destination outside vendor directory')
    if not archive.exists():
        with urllib.request.urlopen(url, timeout=90) as response:
            archive.write_bytes(response.read())
    with zipfile.ZipFile(archive) as z:
        for member in z.infolist():
            parts = member.filename.split('/')[1:]
            if not parts or not any(parts):
                continue
            path = target.joinpath(*parts).resolve()
            if not path.is_relative_to(target):
                raise ValueError('Archive traversal')
            if member.is_dir():
                path.mkdir(parents=True, exist_ok=True)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(z.read(member))
    print(f'{name}: official revision {rev} ready', flush=True)
    return dict(name=name, revision=rev, url=url)

with ThreadPoolExecutor(max_workers=4) as pool:
    provenance = list(pool.map(retrieve, manifest['packages']))
(ROOT / 'dependency-provenance.json').write_text(
    json.dumps({'mathlib_tag': 'v4.33.0', 'dependencies': provenance}, indent=2) + '\n')

"""Verify source identities, dependency pins, the Lake build and the joint kernel audit."""
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys

root = Path(__file__).resolve().parent
formal = root / "formal"
evidence = root / "verification"
records = (evidence / "modules.sha256").read_text().splitlines()
expected = dict(record.split("  ", 1)[::-1] for record in records)
actual = {p.name: sha256(p.read_bytes()).hexdigest() for p in formal.glob("*.lean")}
if actual != expected:
    sys.exit("Source set or digest differs from the published verification.")
for pin in json.loads((evidence / "dependency-pins.json").read_text()):
    dependency = formal / ".lake" / "packages" / pin["name"]
    rev = subprocess.check_output(["git","-C",str(dependency),"rev-parse","HEAD"],text=True).strip()
    dirty = subprocess.check_output(["git","-C",str(dependency),"status","--porcelain","--untracked-files=no"],text=True).strip()
    if rev != pin["pin"] or dirty:
        sys.exit(f"Dependency differs from recorded checkout: {pin['name']}")
version = subprocess.check_output(["lake","env","lean","--version"],cwd=formal,text=True)
if "4.24.0" not in version or "797c613eb9b6" not in version:
    sys.exit(f"Unexpected toolchain: {version}")
subprocess.run(["lake","build"],cwd=formal,check=True)
subprocess.run(["lake","env","lean","--root="+str(evidence),"-DwarningAsError=true",str(evidence / "AllModules.lean")],cwd=formal,check=True)

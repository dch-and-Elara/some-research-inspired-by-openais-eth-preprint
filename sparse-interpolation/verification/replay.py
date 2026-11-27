"""Rebuild every paper module with pinned dependencies and audit its named axiom outputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

FORMAL = Path(__file__).resolve().parents[1] / "formal"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_REPORT = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
SOURCES = {p.stem: p for p in FORMAL.glob("*.lean")}


def run(command, **kwargs):
    return subprocess.run(command, text=True, encoding="utf-8", capture_output=True, **kwargs)


def dependency_paths(packages, extra):
    pins = json.loads((FORMAL / "lake-manifest.json").read_text())
    roots = []
    for pin in pins["packages"]:
        repo = packages / pin["name"]
        rev = run(["git", "-C", repo, "rev-parse", "HEAD"], check=True).stdout.strip()
        dirty = run(["git", "--no-optional-locks", "-C", repo, "status", "--porcelain", "--untracked-files=no"], check=True).stdout
        if rev != pin["rev"] or dirty:
            raise ValueError(f"Dependency checkout differs: {pin['name']}")
        print(f"{pin['name']} {rev}", flush=True)
        roots.append(repo / ".lake/build/lib/lean")
    if extra:
        roots.insert(0, extra)
    for root in roots:
        for module in SOURCES:
            if (root / f"{module}.olean").exists():
                raise ValueError(f"Dependency cache contains paper module {module}")
    return roots


def compile_module(name, lean, build, env):
    src = SOURCES[name]
    source = src.read_text(encoding="utf-8-sig")
    if re.search(r"\b(?:sorry|admit|sorryAx)\b|^\s*(?:private\s+)?axiom\s", source, re.M):
        raise ValueError(f"Forbidden declaration or placeholder in {name}")
    cmd = [lean, "-j1", "-DwarningAsError=true", "-o", build / f"{name}.olean", src.name]
    result = run(cmd, cwd=FORMAL, env=env)
    output = result.stdout + result.stderr
    if result.returncode or re.search(r"\b(?:warning|error):", output):
        raise RuntimeError(f"{name}: {output}")
    reports = AXIOM_REPORT.findall(output)
    requested = re.findall(r"^\s*#print\s+axioms\s+(\S+)", source, re.M)
    names = [n for n, _ in reports]
    if len(names) != len(requested) or any(
        actual != query and not actual.endswith("." + query)
        for actual, query in zip(names, requested)
    ):
        raise ValueError(f"Unexpected axiom check names in {name}: {reports} vs {requested}")
    for declaration, axioms in reports:
        if axioms and not {a.strip() for a in axioms.split(",")} <= ALLOWED:
            raise ValueError(f"Unapproved axiom in {declaration}")
    digest = hashlib.sha256(src.read_bytes()).hexdigest()
    return len(reports), f"{digest}  {src.name}\nLean exit 0\n{output.rstrip()}"


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("build", type=Path, help="new output directory (must not exist)")
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--packages", type=Path, default=FORMAL / ".lake/packages")
    parser.add_argument("--extra-deps", type=Path, help="optional compiled Mathlib dependency overlay")
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    version = run([args.lean, "--version"], cwd=FORMAL, check=True).stdout.strip()
    if "4.24.0," not in version or "797c613eb9b6d4ec95db23e3e00af9ac6657f24b" not in version:
        raise ValueError(version)
    print(version, flush=True)
    roots = dependency_paths(args.packages.resolve(), args.extra_deps)
    build = args.build.resolve()
    build.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(str(p) for p in [build, *roots]))
    dependencies = {}
    for name, src in SOURCES.items():
        imports = re.findall(r"^import\s+(\w+)", src.read_text(encoding="utf-8-sig"), re.M)
        dependencies[name] = set(imports) & SOURCES.keys()
    done, running, checks = set(), {}, 0
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while dependencies or running:
            for name in sorted(list(dependencies)):
                if len(running) < args.jobs and dependencies[name] <= done:
                    running[pool.submit(compile_module, name, args.lean, build, env)] = name
                    del dependencies[name]
            if not running:
                raise ValueError("Cyclic local imports")
            for future in wait(running, return_when=FIRST_COMPLETED).done:
                count, record = future.result()
                print(record, flush=True)
                checks += count
                done.add(running.pop(future))
    print(f"Rebuilt {len(done)} paper modules with {checks} axiom checks.", flush=True)


if __name__ == "__main__":
    main()

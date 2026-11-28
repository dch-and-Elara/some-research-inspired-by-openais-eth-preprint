"""Reconstruct, verify and replay the two published Paper 6 Lean variants."""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from hashlib import file_digest, sha256
import heapq
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
LEAN_COMMIT = "797c613eb9b6d4ec95db23e3e00af9ac6657f24b"
MATHLIB_COMMIT = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
TOOLCHAIN = "leanprover/lean4:v4.24.0"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")
PRINT_AXIOMS = re.compile(r"^\s*#print\s+axioms\s+([^\s]+)\s*$", re.M)
AXIOM_REPORT = re.compile(
    r"^'([^\n]+?)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$",
    re.M,
)
DIAGNOSTIC = re.compile(r"^(?:.*:\d+:\d+: )?(?:warning|error)(?:\([^)\n]*\))?:", re.M)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def digest(data):
    return sha256(data).hexdigest()


def file_hash(path):
    with path.open("rb") as stream:
        return file_digest(stream, "sha256").hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True)+"\n", encoding="utf8")


def reports_in(text):
    return [[name, sorted(x.strip() for x in axioms.split(",") if x.strip())]
            for name, axioms in AXIOM_REPORT.findall(text)]


def check_reports(text, names, exact=False):
    found = reports_in(text)
    actual = [name for name, _ in found]
    require(not DIAGNOSTIC.search(text), "Lean warning or error")
    require(len(actual)==len(names) and all(
        got == expected or (not exact and got.endswith("." + expected))
        for got, expected in zip(actual, names)), "wrong axiom-report names or order")
    require({a for _, axioms in found for a in axioms} <= STANDARD_AXIOMS, "unexpected axiom")
    return found


def decomment(source):
    """Strip Lean comments, preserving strings, line breaks, and token separation."""
    tokens = re.compile(r'"(?:\\.|[^"\\])*"|--[^\r\n]*|/-|-/')
    result = []
    depth = 0
    at = 0
    while match := tokens.search(source, at):
        if depth:
            # A quoted string or line-comment marker inside a block comment
            # does not hide its closing delimiter.
            start = match.start()
            block = re.search(r"/-|-/", source[start:])
            require(block is not None, "unterminated Lean block comment")
            end = start + block.end()
            result.append(re.sub(r"[^\r\n]", " ", source[at:end]))
            depth += 1 if block.group() == "/-" else -1
            at = end
        else:
            result.append(source[at:match.start()])
            token = match.group()
            if token == "/-":
                depth = 1
            result.append(token if token.startswith('"') else " " * len(token))
            at = match.end()
    require(depth == 0, "unterminated Lean block comment")
    result.append(source[at:])
    return "".join(result)


def imports(source):
    """Read the leading Lean header of this flat source corpus."""
    found = []
    for line in decomment(source).splitlines():
        fields = line.split()
        if not fields or fields in (["module"], ["prelude"]):
            continue
        if "import" not in fields or fields[:fields.index("import")] not in (
                [], ["public"], ["meta"], ["public", "meta"]):
            break
        after = fields[fields.index("import") + 1:]
        if after and after[0] == "all":
            after = after[1:]
        require(after and all(MODULE.fullmatch(x) for x in after),
                f"unsupported Lean import header: {line!r}")
        found.extend(after)
    return sorted(set(found))


def closure(index, roots):
    pending = list(roots)
    included = set()
    while pending:
        name = pending.pop()
        require(name in index, f"missing project root {name}")
        if name not in included:
            included.add(name)
            pending.extend(dep for dep in index[name]["imports"] if dep in index)
    return {m: index[m] for m in sorted(included)}


def dependency_order(index):
    deps = {m: set(info["imports"]) & index.keys() for m, info in index.items()}
    successors = {m: [] for m in index}
    pending = {m: len(ds) for m, ds in deps.items()}
    for m, ds in deps.items():
        for dep in ds:
            successors[dep].append(m)
    ready = [m for m, n in pending.items() if n == 0]
    heapq.heapify(ready)
    counts = pending.copy()
    order = []
    while ready:
        m = heapq.heappop(ready)
        order.append(m)
        for child in successors[m]:
            counts[child] -= 1
            if not counts[child]:
                heapq.heappush(ready, child)
    require(len(order) == len(index), f"cycle involving {sorted(index.keys() - set(order))}")
    return order, pending, successors

def read_index():
    data = load(HERE / "manifest.json")
    require(data["format"] == 1 and set(data["variants"]) == {"main", "binary"}, "bad package format")
    return data["variants"]


def source_path(variant, module, row):
    require(MODULE.fullmatch(module) and "." not in module, f"invalid flat module name: {module}")
    layer = row["layer"]
    require(layer in {"shared", variant}, f"unexpected source layer for {module}")
    return HERE / "sources" / layer / (module + ".lean")


def verify_sources():
    plans = read_index()
    used = set()
    for variant, plan in plans.items():
        index = plan["sources"]
        require(len(index) == {"main": 3136, "binary": 1483}[variant], "unexpected module count")
        for module, row in index.items():
            file = source_path(variant, module, row)
            payload = file.read_bytes()
            require(digest(payload) == row["sha256"], f"{variant}/{module}: SHA-256 mismatch")
            text = payload.decode("utf-8-sig")
            require(imports(text) == row["imports"], f"{variant}/{module}: import list mismatch")
            require(PRINT_AXIOMS.findall(decomment(text)) == row["prints"],
                    f"{variant}/{module}: axiom probe list mismatch")
            used.add(file)
        expected_audit = HERE / "checks" / variant / "R119ReplayEndpointAudit.lean"
        require(file_hash(expected_audit) == plan["endpoint_source_sha256"],
                f"{variant}: endpoint audit source hash mismatch")
        require(set(plan["endpoints"]) <= index.keys(), f"{variant}: missing endpoint modules")
        dependency_order(index)
        print(f"{variant}: verified {len(index)} project sources and endpoint audit source", flush=True)
    require(used == set((HERE / "sources").rglob("*.*")), "extra files in source layers")
    return plans


def verify_evidence(plans):
    summary = load(HERE/"evidence/summary.json")
    for kind, plan in plans.items():
        folder = HERE/"evidence"/kind
        rows = load(folder/"modules.json")
        info = summary["variants"][kind]
        require(rows.keys() == plan["sources"].keys(), f"{kind}: incomplete historical receipts")
        for name, row in rows.items():
            require(row["source_sha256"] == plan["sources"][name]["sha256"],
                    f"{kind}/{name}: receipt source mismatch")
            require({a for _, axioms in row["axioms"] for a in axioms} <= STANDARD_AXIOMS,
                    f"{kind}/{name}: unexpected historical axiom")
            order = plan["sources"][name]["prints"]
            actual = [decl for decl, _ in row["axioms"]]
            require(len(order) == len(actual) and all(
                got == want or got.endswith("."+want) for got, want in zip(actual, order)),
                f"{kind}/{name}: historical axiom name or order mismatch")
        require(sum(len(row["axioms"]) for row in rows.values()) == info["module_axiom_reports"],
                f"{kind}: historical report count mismatch")
        names = endpoint_names(plan)
        log = folder/"endpoints.log"
        require(file_hash(log) == info["endpoint_log_sha256"], f"{kind}: endpoint log hash mismatch")
        text = log.read_text(encoding="utf8")
        require(
            check_reports(text, names, exact=True) == load(folder/"endpoints.json")["axioms"],
            f"{kind}: historical endpoint receipt mismatch")
        require(text.splitlines().count("R119 same-run audit passed") == len(plan["same_runs"]),
                f"{kind}: historical same-run check count mismatch")
        for name in info["recompiled_in_final_pass"]:
            require(file_hash(folder/f"{name}.log") == rows[name]["log_sha256"],
                    f"{kind}/{name}: final compile log hash mismatch")
            require(check_reports((folder/f"{name}.log").read_text(encoding="utf8"),
                                  plan["sources"][name]["prints"]) == rows[name]["axioms"],
                    f"{kind}/{name}: final compile output mismatch")
        print(f"{kind}: checked historical evidence for {len(rows)} modules and {len(names)} endpoints",
              flush=True)


def endpoint_names(plan):
    return [name for module in sorted(plan["endpoints"]) for name in plan["endpoints"][module]]


def tool(name):
    # Resolve before changing cwd so relative executable paths keep their meaning.
    if Path(name).is_file():
        return str(Path(name).resolve())
    path = shutil.which(name)
    require(path is not None, f"executable not found: {name}")
    return path


def clean_env():
    return {k: v for k, v in os.environ.items()
            if k.upper() not in {"LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"}}


def check_toolchain(lean, env, cwd):
    version = subprocess.check_output([lean, "--version"], env=env, cwd=cwd, text=True).strip()
    require("version 4.24.0," in version and LEAN_COMMIT in version, f"wrong Lean toolchain: {version}")
    prefix = subprocess.check_output([lean, "--print-prefix"], env=env, cwd=cwd, text=True).strip()
    return version, Path(prefix)/"lib/lean"


def package_pin():
    rows = load(HERE/"pins.json")["packages"]
    require(rows["mathlib"] == MATHLIB_COMMIT, "package pin mismatch")
    return rows


def package_libraries(packages, pins):
    require(packages.is_dir(), "missing Lake packages directory")
    result = []
    for name, expected in sorted(pins.items()):
        checkout = packages/name
        head = subprocess.check_output(["git","-C",str(checkout),"rev-parse","HEAD"], text=True).strip()
        require(head==expected, f"{name}: expected Git HEAD {expected}, got {head}")
        dirty = subprocess.check_output(["git","--no-optional-locks","-C",str(checkout),"status","--porcelain",
                                         "--untracked-files=no","--ignore-submodules=none"],text=True)
        require(not dirty.strip(), f"{name}: modified tracked dependency files")
        lib = checkout/".lake/build/lib/lean"
        if lib.is_dir():
            result.append(lib)
    return result


def verify_configured_imports(index, external_paths):
    for module, row in index.items():
        name = Path(*module.split(".")).with_suffix(".olean")
        require(not any((directory/name).exists() for directory in external_paths),
                f"prebuilt object shadows project module {module}")
        for dep in set(row["imports"])-index.keys():
            obj = Path(*dep.split(".")).with_suffix(".olean")
            require(any((directory/obj).is_file() for directory in external_paths),
                    f"{module}: missing external {dep}; prepare dependencies before replay")


def setup(args):
    dest = Path(args.output).resolve()
    require(not dest.exists(), f"dependency checkout already exists: {dest}")
    subprocess.run(["git","init",str(dest)], check=True)
    subprocess.run(["git","-C",str(dest),"remote","add","origin",
                    "https://github.com/leanprover-community/mathlib4.git"], check=True)
    subprocess.run(["git","-C",str(dest),"fetch","--depth","1","origin",MATHLIB_COMMIT], check=True)
    subprocess.run(["git","-C",str(dest),"checkout","--detach","FETCH_HEAD"], check=True)
    require((dest/"lean-toolchain").read_text(encoding="utf8").strip()==TOOLCHAIN, "Mathlib toolchain mismatch")
    rows = load(dest/"lake-manifest.json")["packages"]
    pins = package_pin()
    require({row["name"]:row["rev"] for row in rows}=={n:r for n,r in pins.items() if n!="mathlib"},
            "Mathlib dependency lock mismatch")
    env = clean_env()
    check_toolchain(tool(args.lean), env, dest)
    lake = tool(args.lake)
    # Lake clones dependencies from the checkout's pinned manifest.
    if args.build_deps:
        subprocess.run([lake,"--no-cache","build","Mathlib"], cwd=dest, env=env, check=True)
    else:
        subprocess.run([lake,"exe","cache","get"], cwd=dest, env=env, check=True)
    package_libraries(dest/".lake/packages",{n:r for n,r in pins.items() if n!="mathlib"})
    require((dest/".lake/build/lib/lean/Mathlib/Tactic.olean").is_file(), "Mathlib artifacts missing")
    print(f"Use --mathlib {dest} for replay", flush=True)


def replay(args):
    plans = verify_sources()
    plan = plans[args.variant]
    index = plan["sources"]
    scoped = bool(args.target)
    if scoped:
        index = closure(index, args.target)
    order, pending, successors = dependency_order(index)
    lean = tool(args.lean)
    env = clean_env()
    version, core = check_toolchain(lean, env, HERE)
    pins = package_pin()
    if args.package_dir:
        libraries = package_libraries(Path(args.package_dir).resolve(), pins)
    else:
        mathlib = Path(args.mathlib).resolve()
        head = subprocess.check_output(["git","-C",str(mathlib),"rev-parse","HEAD"],text=True).strip()
        dirty = subprocess.check_output(["git","--no-optional-locks","-C",str(mathlib),"status","--porcelain",
                                         "--untracked-files=no","--ignore-submodules=none"],text=True)
        require(head == MATHLIB_COMMIT and not dirty.strip(), "Mathlib checkout is dirty or at wrong revision")
        libraries = [mathlib/".lake/build/lib/lean", *package_libraries(mathlib/".lake/packages",
                        {name:rev for name,rev in pins.items() if name!="mathlib"})]
    verify_configured_imports(plan["sources"], [core,*libraries])
    out = Path(args.output).resolve()
    out.mkdir(parents=True, exist_ok=False)
    src, obj, logs = [out/x for x in ("src","olean","logs")]
    for path in (src,obj,logs):
        path.mkdir()
    for name, row in index.items():
        target = src/(name+".lean")
        shutil.copyfile(source_path(args.variant,name,row),target)
        require(file_hash(target)==row["sha256"],f"copied source changed: {name}")
    env["LEAN_PATH"] = os.pathsep.join(map(str,[obj,*libraries]))
    write_json(out/"environment.json", {"lean":version,"lean_path":env["LEAN_PATH"],"packages":pins})
    write_json(out/"plan.json", {"variant":args.variant,"targets":args.target,"sources":index,
                                "run_release_endpoints":not scoped})
    print(f"{args.variant}: {'target closure' if scoped else 'full replay'}, {len(index)} modules", flush=True)

    def run(file, log, names, output=None):
        cmd = [lean,"-j","1","-DwarningAsError=true",f"--root={src}"]
        if output:
            cmd.extend(["-o",str(output)])
        cmd.append(str(file))
        start = time.monotonic()
        with log.open("wb") as stream:
            rc = subprocess.run(cmd,cwd=src,env=env,stdout=stream,stderr=subprocess.STDOUT).returncode
        text = log.read_text(encoding="utf8",errors="replace")
        row = {"returncode":rc,"seconds":round(time.monotonic()-start,2),
               "log_sha256":file_hash(log),"source_sha256":file_hash(file),
               "expected_names":names,"axioms":reports_in(text),"passed":False}
        if output and output.is_file():
            row["object_sha256"] = file_hash(output)
        try:
            require(rc==0 and (not output or output.is_file()), f"Lean exit {rc} or object missing")
            check_reports(text,names,exact=output is None)
            if output:
                require(row["source_sha256"]==index[file.stem]["sha256"], "source changed during build")
            else:
                matches = text.splitlines().count("R119 same-run audit passed")
                require(matches==len(plan["same_runs"]), "wrong number of same-run checks")
                row["same_run_checks"]=matches
            row["passed"]=True
        except ValueError as e:
            row["failure"]=str(e)
        write_json(log.with_suffix(".json"),row)
        return row

    def compile_module(name):
        return run(src/(name+".lean"),logs/(name+".log"),index[name]["prints"],obj/(name+".olean"))

    ready = [m for m in order if pending[m]==0]
    heapq.heapify(ready)
    results, running = {}, {}
    failed = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while running or (ready and not failed):
            while ready and not failed and len(running)<args.jobs:
                module=heapq.heappop(ready)
                running[pool.submit(compile_module,module)]=module
            completed, _=wait(running,return_when=FIRST_COMPLETED)
            for future in sorted(completed,key=running.__getitem__):
                module=running.pop(future)
                row=results[module]=future.result()
                print(f"{len(results)}/{len(index)} {module} {'PASS' if row['passed'] else 'FAIL'}",flush=True)
                if not row["passed"]:
                    failed.append(module)
                    continue
                for child in successors[module]:
                    pending[child]-=1
                    if pending[child]==0:
                        heapq.heappush(ready,child)
    endpoint = None
    if not scoped and not failed and len(results)==len(index):
        path=src/"R119ReplayEndpointAudit.lean"
        shutil.copyfile(HERE/"checks"/args.variant/path.name,path)
        require(file_hash(path)==plan["endpoint_source_sha256"], "endpoint stage changed")
        endpoint=run(path,logs/"endpoints.log",endpoint_names(plan))
    passed=not failed and len(results)==len(order) and (scoped or endpoint and endpoint["passed"])
    write_json(out/"summary.json",{"passed":bool(passed),"variant":args.variant,
        "scope":"target closure" if scoped else "complete variant", "targets":args.target,
        "modules":len(index),"attempted":len(results),"failed_modules":failed,
        "project_objects_reused":0,"module_axiom_reports":sum(len(row["axioms"]) for row in results.values()),
        "endpoints":endpoint})
    return 0 if passed else 1


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    commands=parser.add_subparsers(dest="command",required=True)
    commands.add_parser("verify",help="verify all archived source bytes and historical evidence")
    extract=commands.add_parser("export",help="materialize one complete project source tree")
    extract.add_argument("variant",choices=("main","binary"))
    extract.add_argument("output")
    deps=commands.add_parser("setup",help="acquire the pinned external dependencies in a new directory")
    deps.add_argument("output")
    deps.add_argument("--lean",default="lean")
    deps.add_argument("--lake",default="lake")
    deps.add_argument("--build-deps",action="store_true",help="compile external dependencies instead of downloading their objects")
    build=commands.add_parser("replay",help="compile a variant from empty project object directories")
    build.add_argument("variant",choices=("main","binary"))
    build.add_argument("output")
    build.add_argument("--lean",default="lean")
    pin=build.add_mutually_exclusive_group(required=True)
    pin.add_argument("--mathlib",help="root of a pinned standalone Mathlib checkout")
    pin.add_argument("--package-dir",help="existing Lake package directory containing pinned Mathlib and dependency objects")
    build.add_argument("--jobs",type=int,choices=range(1,17),default=2)
    build.add_argument("--target",action="append",default=[],metavar="MODULE",
                       help="compile only this module and its dependency closure; repeatable")
    args=parser.parse_args()
    if args.command=="setup":
        setup(args)
    elif args.command=="replay":
        return replay(args)
    else:
        plans=verify_sources()
        if args.command=="verify":
            verify_evidence(plans)
        else:
            dest=Path(args.output)
            dest.mkdir(parents=True,exist_ok=False)
            for name,row in plans[args.variant]["sources"].items():
                target=dest/(name+".lean")
                shutil.copyfile(source_path(args.variant,name,row),target)
                require(file_hash(target)==row["sha256"],f"exported source changed: {name}")
            name="R119ReplayEndpointAudit.lean"
            shutil.copyfile(HERE/"checks"/args.variant/name,dest/name)
            require(file_hash(dest/name)==plans[args.variant]["endpoint_source_sha256"],"exported audit changed")
    return 0


if __name__=="__main__":
    try:
        sys.exit(main())
    except (ValueError,OSError,subprocess.CalledProcessError) as e:
        print(f"paper6: {e}",file=sys.stderr)
        sys.exit(2)

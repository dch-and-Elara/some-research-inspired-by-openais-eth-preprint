"""Build the pinned project and audit the axioms of its public theorems."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent
FORMAL = ROOT / "formal"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def recorded(args, log):
    with log.open("wb") as stream:
        subprocess.run(args, cwd=FORMAL, stdout=stream, stderr=subprocess.STDOUT, check=True)
    return log.read_text(encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--logs", type=Path, required=True)
    logs = parser.parse_args().logs.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    sources = sorted(FORMAL.glob("*.lean"))
    modules = [p.stem for p in sources]
    for p in sources:
        if re.search(r"\b(sorry|admit|sorryAx|axiom|implemented_by|native_decide)\b", p.read_text("utf-8")):
            raise ValueError(f"Unresolved proof or trust annotation in {p.name}")
    named = set((ROOT / "named-declarations.txt").read_text(encoding="utf-8").splitlines())
    version = recorded(["lake", "env", "lean", "--version"], logs / "toolchain.txt")
    expected_version = (FORMAL / "lean-toolchain").read_text().strip().split(":v")[-1]
    if f"version {expected_version}," not in version:
        raise ValueError(f"Unexpected toolchain: {version}")
    packages = json.loads((FORMAL / "lake-manifest.json").read_text(encoding="utf-8"))["packages"]
    revisions = []
    for pkg in packages:
        checkout = FORMAL / ".lake" / "packages" / pkg["name"]
        actual = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
        if actual != pkg["rev"]:
            raise ValueError(f"Unexpected revision for {pkg['name']}")
        if subprocess.check_output(["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=no"]):
            raise ValueError(f"Locally modified dependency: {pkg['name']}")
        revisions.append(f"{pkg['name']} {actual}")
    (logs / "dependencies.txt").write_text("\n".join(revisions) + "\n", encoding="utf-8")
    recorded(["lake", "build"], logs / "build.txt")
    imports = "".join("import " + m + "\n" for m in modules)
    names_array = ", ".join('"' + m + '"' for m in modules)
    with tempfile.TemporaryDirectory(dir=FORMAL / ".lake") as tmp:
        inventory = Path(tmp) / "Inventory.lean"
        inventory.write_text(imports + """
open Lean Elab Command
run_cmd
  let env ← getEnv
  let wanted : Array String := #[""" + names_array + """]
  for (n, info) in env.constants.toList do
    if info matches .thmInfo _ then
      if !n.isInternal then
        if let some i := env.getModuleIdxFor? n then
          let modName := env.header.moduleNames[i.toNat]!
          if wanted.contains modName.toString then
            liftIO <| IO.println ("AUDIT_DECL " ++ n.toString)
""", encoding="utf-8")
        output = recorded(["lake", "env", "lean", str(inventory)], logs / "inventory.txt")
        theorems = sorted(set(re.findall(r"^AUDIT_DECL (\S+)$", output, re.M)))
        if not theorems:
            raise ValueError("No public local theorems found")
        audit = Path(tmp) / "Audit.lean"
        audit.write_text(imports + "".join("#print axioms " + n + "\n" for n in sorted(set(theorems) | named)), encoding="utf-8")
        output = recorded(["lake", "env", "lean", str(audit)], logs / "axioms.txt")
    reports = {}
    for name, axioms in re.findall(r"^'(.+?)' depends on axioms:\s*\[([^\]]*)\]", output, re.M):
        reports[name] = {x.strip() for x in axioms.split(",") if x.strip()}
    for name in re.findall(r"^'(.+?)' does not depend on any axioms", output, re.M):
        reports[name] = set()
    if (set(theorems) | named) != set(reports):
        raise ValueError(f"Unmatched declarations: {(set(theorems) | named) ^ set(reports)}")
    for name, deps in reports.items():
        if deps - STANDARD:
            raise ValueError(f"Unexpected axioms for {name}: {deps - STANDARD}")
    checked = sources + [FORMAL / n for n in ("lean-toolchain", "lake-manifest.json", "lakefile.toml")]
    (logs / "source-sha256.txt").write_text("".join(
        hashlib.sha256(p.read_bytes()).hexdigest() + "  formal/" + p.name + "\n" for p in checked
    ), encoding="utf-8")
    result = f"Verified {len(sources)} Lean source modules and {len(theorems)} public theorem declarations. All {len(named)} named declarations passed the axiom audit."
    (logs / "result.txt").write_text(result + "\n", encoding="utf-8")
    print(result)


if __name__ == "__main__":
    main()

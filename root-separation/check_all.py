"""Run the finite examples from the release and check its immutable source manifest."""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest():
    manifest = ROOT / "SOURCE_MANIFEST.json"
    for name, expected in json.loads(manifest.read_text(encoding="utf-8")).items():
        if digest(ROOT / name) != expected:
            raise ValueError(f"Release file differs from the manifest: {name}")
    return digest(manifest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--logs", required=True, type=Path)
    parser.add_argument("--upstream-sources", type=Path,
                        help="Directory containing the four TeX files of the cited upstream revision")
    args = parser.parse_args()
    logs = args.logs.resolve()
    before = check_manifest()
    logs.mkdir(parents=True, exist_ok=True)
    results = []
    for source in sorted((ROOT / "tests").glob("*.py")):
        with (logs / (source.stem + ".txt")).open("wb") as stream:
            subprocess.run([sys.executable, "-X", "utf8", str(source)], cwd=ROOT,
                           stdout=stream, stderr=subprocess.STDOUT, check=True)
        results.append(source.name)
    if args.upstream_sources:
        references = json.loads((ROOT / "upstream.json").read_text(encoding="utf-8"))
        observed = {name: digest(args.upstream_sources / name) for name in references}
        if references != observed:
            raise ValueError("Upstream source hashes differ from the cited revision")
        (logs / "upstream_sources.json").write_text(json.dumps(observed, indent=2) + "\n",
                                                     encoding="utf-8")
    if before != check_manifest():
        raise ValueError("Running the finite checks changed the release manifest")
    summary = f"Passed {len(results)} finite checks. Release source manifest verified before and after."
    (logs / "result.txt").write_text(summary + "\n", encoding="utf-8")
    print(summary)


if __name__ == "__main__":
    main()

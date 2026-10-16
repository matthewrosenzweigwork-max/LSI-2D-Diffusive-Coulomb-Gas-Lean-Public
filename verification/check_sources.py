import hashlib, json
from pathlib import Path
root = Path(__file__).resolve().parents[1]
m = json.loads((root / "verification/PUBLIC_SOURCE_MANIFEST.json").read_text())
for f in m["files"]:
    b = (root / f["path"]).read_bytes()
    if len(b) != f["bytes"] or hashlib.sha256(b).hexdigest() != f["sha256"]:
        raise SystemExit("Source identity mismatch: " + f["path"])
print("Verified", len(m["files"]), "frozen source/configuration files.")

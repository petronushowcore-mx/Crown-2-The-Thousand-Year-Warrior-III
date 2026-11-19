"""Mutations of isolated mathematical models."""
MUTATIONS = [('t_W01_cancelled_seams', 'return all(membership(labels))', 'return sum(labels) == 0', 'collapse cancelled seams into the same total'), ('t_W02_sufficient_compression', 'return decoder(key, verdict) is not None', 'return len(set(key)) == len(key)', 'demand injective history for one verdict'), ('t_W03_exists_vs_chosen', 'return candidate is not None', 'return candidate is not None and all(v == 0 for v in verdict)', 'mistake an arbitrarily chosen constant decoder for existential decoding'), ('t_W04_linear_kernel_bridge', 'return all(dot(a, v) == 0 for v in kernel_basis(r))', 'return all(dot(r, v) == 0 for v in kernel_basis(a))', 'reverse kernel inclusion; zero transported functional slips through'), ('t_W05_restricted_zero_fibre', 'domain = sorted(set(witnesses) | {(0, 0)})', 'domain = sorted(set(witnesses))', 'omit origin so the lost witness shares no negative verdict'), ('t_W06_selected_vs_global_loss', 'if not any(survives):', 'if not all(survives):', 'call a partial loss total'), ('t_W07_silent_intervention', 'return capability or request', 'return request', 'erase spontaneous continuation'), ('SURVIVE:rename', 'def dot(a, v):\n    return sum(x*y for x, y in zip(a, v))', 'def dot(a, vector):\n    return sum(x*y for x, y in zip(a, vector))', 'rename a local parameter'), ('REACH:rename', 'def dot(a, v):\n    return sum(x*y for x, y in zip(a, v))', 'def dot(a, v):\n    return 1 + sum(x*y for x, y in zip(a, v))', 'destroy same pairing site')]
# Further facts inside named checks, each broken by its own mutation of the model.
MUTATIONS += [
    ('REACH:later-seam', 'return all(membership(labels))', 'return bool(membership(labels)[0])',
     'admit a history whenever its first seam is admitted'),
    ('REACH:factorisation', 'return decoder(key, verdict) is not None', 'return tuple(key) == tuple(verdict)',
     'read factorisation through a decoder as literal equality of key and verdict'),
    ('REACH:bridge', 'verdicts = tuple(int(dot(a, v) != 0) for v in carrier)', 'verdicts = tuple(0 for v in carrier)',
     'erase the nonzero verdict read through the linear functional on the carrier'),
    ('REACH:selected-loss', 'if not any(survives):', 'if not any(r):',
     'take loss of every selected witness to mean a zero transported functional'),
    ('REACH:decoder-applied', 'return out', 'return {reading: not verdict for reading, verdict in out.items()}',
     'return a decoder that exists but answers every reading wrongly'),
    ('REACH:decoder-empty', 'return out', 'return {}',
     'return an empty decoder that is never None'),
]
# The named check each REACH case must fail first; a label without an entry is a registry error.
REACH_FIRST = {'rename': 't_W04_linear_kernel_bridge', 'later-seam': 't_W01_cancelled_seams',
               'factorisation': 't_W02_sufficient_compression', 'bridge': 't_W04_linear_kernel_bridge',
               'selected-loss': 't_W06_selected_vs_global_loss',
               'decoder-applied': 't_W01_cancelled_seams', 'decoder-empty': 't_W01_cancelled_seams'}

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import re


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(source, folder):
    program = folder / "harness.py"
    output = folder / "outcomes.json"
    program.write_text(source, encoding="utf-8", newline="\n")
    if output.exists():
        output.unlink()
    try:
        proc = subprocess.run([sys.executable, "-B", *(["-O"] * sys.flags.optimize), str(program), "--teeth", "--json", str(output)], capture_output=True, text=True, encoding="utf-8", timeout=30)
    except subprocess.TimeoutExpired:
        return {"rc": "TIMEOUT", "rows": [], "stdout": "", "stderr": "timeout after 30 s"}
    rows = json.loads(output.read_text(encoding="utf-8")) if output.exists() else []
    return {"rc": proc.returncode, "rows": rows, "stdout": proc.stdout, "stderr": proc.stderr}


def streams_clean(result, rows):
    """Every stdout line is the summary or the FAIL line of a failing check, and stderr is empty;
    an unrecognised line or any stderr output fails the case."""
    if result["stderr"].strip():
        return False
    failing = {row["name"] for row in rows if row["status"] == "FAIL"}
    summary = "teeth: %d/%d" % (len(rows) - len(failing), len(rows))
    for line in result["stdout"].splitlines():
        match = re.match(r"^FAIL (t_\w+):( |$)", line)
        if line != summary and not (match and match.group(1) in failing):
            return False
    return True


def verdict_controls():
    """The streams check accepts clean output and refuses a stray stdout line, a stderr line and the
    FAIL line of a passing check."""
    rows = [{"name": "t_a", "status": "PASS"}, {"name": "t_b", "status": "FAIL"}]
    clean = {"rc": 1, "rows": rows, "stdout": "FAIL t_b: detail\nteeth: 1/2\n", "stderr": ""}
    if not streams_clean(clean, rows):
        raise SystemExit("VERDICT_CONTROL: clean streams refused")
    if not streams_clean(dict(clean, stdout="FAIL t_b:\nteeth: 1/2\n"), rows):
        raise SystemExit("VERDICT_CONTROL: a bare FAIL line refused")
    for name, broken in (("a stray stdout line", dict(clean, stdout=clean["stdout"] + "stray\n")),
                         ("a stderr line", dict(clean, stderr="warning\n")),
                         ("the FAIL line of a passing check", dict(clean, stdout="FAIL t_a: x\n" + clean["stdout"]))):
        if streams_clean(broken, rows):
            raise SystemExit("VERDICT_CONTROL: " + name + " accepted")


def verdict(result, marker, expected):
    rows = result["rows"]
    names = [row["name"] for row in rows]
    if marker.startswith("REACH:"):
        marker = REACH_FIRST[marker[len("REACH:"):]]
    if names != expected or any(row["status"] not in ("PASS", "FAIL") for row in rows):
        return False
    bad = [row["name"] for row in rows if row["status"] != "PASS"]
    summary = "teeth: %d/%d" % (len(rows)-len(bad), len(rows))
    if summary not in result["stdout"].splitlines():
        return False
    if not streams_clean(result, rows):
        return False
    if marker == "BASE" or marker.startswith("SURVIVE:"):
        return result["rc"] == 0 and not bad
    return result["rc"] == 1 and bool(bad) and bad[0] == marker and ("FAIL " + marker + ":") in result["stdout"]


def main():
    verdict_controls()
    here = Path(__file__).resolve().parent
    raw = (here / "harness.py").read_bytes()
    source = raw.decode("utf-8")
    expected = sorted(re.findall(r"^def (t_\w+)\(\):", source, re.M))
    markers = [m[0] for m in MUTATIONS if m[0].startswith("t_")]
    if sorted(markers) != expected or len(markers) != len(set(markers)):
        raise SystemExit("mutation registry does not cover the exact named check set")
    reach = [m[0][len("REACH:"):] for m in MUTATIONS if m[0].startswith("REACH:")]
    if sorted(reach) != sorted(REACH_FIRST) or not set(REACH_FIRST.values()) <= set(expected):
        raise SystemExit("each REACH case needs exactly one entry naming an existing check")
    report = {"harness_sha256": sha(raw), "breaker_sha256": sha(Path(__file__).read_bytes()), "python": sys.version, "optimisation": sys.flags.optimize, "expected_checks": expected, "cases": [], "status": "INCOMPLETE"}
    out = here / ("mutation-report-optimised.json" if sys.flags.optimize else "mutation-report.json")
    def save():
        out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    save()
    with tempfile.TemporaryDirectory(prefix="triad-model-") as temporary:
        folder = Path(temporary)
        base = run(source, folder)
        if not verdict(base, "BASE", expected):
            report["base"] = base
            save()
            raise SystemExit("BASE FAILED: " + base["stdout"] + base["stderr"])
        for marker, old, new, why in MUTATIONS:
            if source.count(old) != 1 or old == new:
                raise SystemExit("mutation anchor not unique or ineffective: " + marker)
            changed = source.replace(old, new)
            result = run(changed, folder)
            ok = verdict(result, marker, expected)
            report["cases"].append({"expected": marker, "reason": why, "ok": ok, "mutant_sha256": sha(changed.encode("utf-8")), **result})
            save()
    passed = sum(case["ok"] for case in report["cases"])
    report["status"] = "PASS" if passed == len(MUTATIONS) else "FAIL"
    save()
    for case in report["cases"]:
        if not case["ok"]:
            print("FAIL mutation " + case["expected"] + ": " + case["stdout"].replace("\n", " | ") + case["stderr"])
    print("mutations: %d/%d; source %s; report %s" % (passed, len(MUTATIONS), report["harness_sha256"][:12], out.name))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())

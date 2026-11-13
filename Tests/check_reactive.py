"""Check that invalid reactive programs are rejected. Run from the repo root."""
import subprocess
import tempfile
from pathlib import Path

cases = {
    "wrong action payload type": (
        'def bad : ST s Unit := do\n let c ← AmountCounters.new\n'
        ' c.ca.enqueue (.increase "wrong")\n',
        "mismatch",
    ),
    "wrong request argument type": (
        'def bad : ST s Int := do\n let c ← AmountCounters.new\n'
        ' sync c.ca.decrease "wrong"\n',
        "mismatch",
    ),
    "missing constructor argument": (
        "network Missing where\n ca := Counter()\n",
        "mismatch",
    ),
    "extra constructor argument": (
        "network Extra where\n ca := Counter(ca, ca)\n",
        "mismatch",
    ),
    "undeclared friend": (
        "reactive Plain where\n state : Int := 0\n"
        " action tick := do\n  let _ := self.friend\n  pure ()\n",
        "friend",
    ),
    "synchronous cycle": (
        "reactive Loop (friend : Loop) where\n"
        " state : Int := 0\n"
        " request up : Int := sync friend.down\n"
        " request down : Int := sync friend.up\n"
        " action tick := pure ()\n",
        "termination",
    ),
    "unknown friend": (
        "network Broken where\n ca := Counter(missing)\n",
        "unknown friend",
    ),
    "unknown message": (
        "def bad : ST s Unit := do\n"
        " let c ← Counters.new\n c.ca.enqueue .missing\n",
        "missing",
    ),
}

for name, (body, expected) in cases.items():
    with tempfile.TemporaryDirectory() as folder:
        source = Path(folder) / "Check.lean"
        source.write_text("import Examples.ReactiveExample\nimport Examples.AmountCounter\n" + body)
        result = subprocess.run(
            ["lake", "env", "lean", str(source)], capture_output=True, text=True
        )
        output = result.stdout + result.stderr
        if result.returncode == 0 or expected not in output.lower():
            raise AssertionError(f"{name}: unexpected compiler result\n{output}")
        print(f"{name}: correctly rejected")

#!/usr/bin/env python3
"""Check literal substrings in Rocq Redirect output (relative to each .expect)."""

import sys
from pathlib import Path


def check(spec):
    ok = True
    logs = {}
    for number, line in enumerate(spec.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = line.split("\t", 2)
        if len(fields) != 3 or not fields[0] or fields[1] not in ("+", "-") or not fields[2]:
            reason = "expected log<TAB>+ or -<TAB>text"
        else:
            name, polarity, text = fields
            if name not in logs:
                try:
                    logs[name] = (spec.parent / name).read_text(encoding="utf-8")
                except (OSError, UnicodeError) as error:
                    logs[name] = error
            log = logs[name]
            if isinstance(log, Exception):
                reason = f"cannot read {name}: {log}"
            elif (text in log) == (polarity == "+"):
                continue
            else:
                reason = f"{name}: {'missing' if polarity == '+' else 'unexpected'} {text!r}"
        print(f"EXPECT FAIL: tests/{spec.name}:{number}: {reason}", file=sys.stderr)
        ok = False
    return ok


def main(args):
    ok = True
    for arg in args:
        spec = Path(arg)
        try:
            ok = check(spec) and ok
        except (OSError, UnicodeError) as error:
            print(f"EXPECT FAIL: tests/{spec.name}:1: {error}", file=sys.stderr)
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

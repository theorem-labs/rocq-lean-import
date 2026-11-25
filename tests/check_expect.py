#!/usr/bin/env python3
"""Check literal substrings in Rocq Redirect output (relative to each .expect)."""

import re
import sys
from pathlib import Path

# A polarity "<=N" compares two heap readings instead of finding a substring:
# its text is the words before a reading, the log must hold that text exactly
# twice, each time followed by " <integer> MiB", and the second integer may
# exceed the first by at most N.
MARGIN = re.compile(r"<=(\d+)")
READING = re.compile(r" (\d+) MiB")


def heap_readings(name, log, text, margin):
    """Why the "<=margin" line for text fails on log, or None when it holds."""
    ends = [found.end() for found in re.finditer(re.escape(text), log)]
    if len(ends) != 2:
        return f"{name}: {len(ends)} readings after {text!r}, expected 2"
    readings = [READING.match(log, end) for end in ends]
    if not all(readings):
        return f"{name}: unreadable reading after {text!r}"
    first, second = (int(reading.group(1)) for reading in readings)
    if second - first <= margin:
        return None
    return f"{name}: second reading {second} MiB exceeds the first, {first} MiB, by more than {margin} MiB"


def check(spec):
    ok = True
    logs = {}
    for number, line in enumerate(spec.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = line.split("\t", 2)
        margin = MARGIN.fullmatch(fields[1]) if len(fields) == 3 else None
        if len(fields) != 3 or not fields[0] or not (fields[1] in ("+", "-") or margin) or not fields[2]:
            reason = "expected log<TAB>+, - or <=N<TAB>text"
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
            elif margin:
                reason = heap_readings(name, log, text, int(margin.group(1)))
                if reason is None:
                    continue
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

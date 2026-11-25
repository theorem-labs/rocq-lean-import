#!/usr/bin/env python3
"""Check the Redirect logs of the tests (relative to each .expect), and clear them before a test compiles.

check_expect.py <test>.expect...
    Check each file. Each line that is not blank or a "#" comment is "<log><TAB><polarity><TAB><text>":
    "+" the log holds the text, "-" it does not, "=" the log is exactly the text (in it, \\n is a line break
    and \\\\ a backslash), "<=N" two heap readings (below). <log> is a Redirect's output in the test's
    directory (LOG_NAME). A missing file, a line that cannot be read, and a file with no such line (empty,
    blank or comments only), fail like a failed assertion.

check_expect.py --rocq <rocq> <arguments>...
    The command tests/Makefile gives Rocq's makefile as ROCQ. Before `<rocq> compile ... <test>.v` it deletes
    the logs that the readable lines of <test>.expect name and the .out file of each Redirect of <test>.v,
    each a LOG_NAME in the test's directory and nothing else, so that a log the compile does not write again
    cannot satisfy an assertion; then it runs <rocq> with the arguments.
"""

import os
import re
import sys
from pathlib import Path

# A polarity "<=N" compares two heap readings instead of finding a substring:
# its text is the words before a reading, the log must hold that text exactly
# twice, each time followed by " <integer> MiB", and the second integer may
# exceed the first by at most N.
MARGIN = re.compile(r"<=(\d+)")
READING = re.compile(r" (\d+) MiB")
# A Redirect command at the start of a line of a test (a commented-out one is not).
REDIRECT = re.compile(r'^\s*Redirect\s+"([^"]+)"', re.MULTILINE)
# The one rule for a log, read by an assertion (check) and deleted before a compile (compile_outputs): the output
# Rocq writes for a Redirect, "<name>.out", as a plain file name in the test's directory (no directory part).
LOG_NAME = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_.+-]*\.out")


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


def unescape(text):
    """The text of an "=" line with its escapes read (\\n, \\\\), or None when it holds another escape."""
    out, rest = [], text
    while "\\" in rest:
        before, rest = rest.split("\\", 1)
        out.append(before)
        if rest[:1] == "n":
            out.append("\n")
        elif rest[:1] == "\\":
            out.append("\\")
        else:
            return None
        rest = rest[1:]
    out.append(rest)
    return "".join(out)


def assertion_lines(spec_text):
    """The (number, line) of each line of a .expect that is not blank or a comment."""
    for number, line in enumerate(spec_text.splitlines(), 1):
        if line.strip() and not line.lstrip().startswith("#"):
            yield number, line


def parse_assertion(line):
    """(log, polarity, text, margin, exact) of an assertion line, or a str: why it cannot be read."""
    fields = line.split("\t", 2)
    polarity = fields[1] if len(fields) == 3 else None
    margin = MARGIN.fullmatch(polarity) if polarity else None
    exact = unescape(fields[2]) if polarity == "=" else None
    if (len(fields) != 3 or not fields[0] or not fields[2]
            or not (polarity in ("+", "-") or margin or exact is not None)):
        return "expected log<TAB>+, -, = or <=N<TAB>text (in an = text, only the escapes \\n and \\\\)"
    if not LOG_NAME.fullmatch(fields[0]):
        return (f"{fields[0]!r} is not a Redirect log: a log is <name>.out in the test's directory "
                "(letters, digits and _.+- only)")
    return fields[0], polarity, fields[2], margin, exact


def check(spec):
    ok = True
    assertions = 0
    logs = {}
    for number, line in assertion_lines(spec.read_text(encoding="utf-8")):
        assertions += 1
        parsed = parse_assertion(line)
        if isinstance(parsed, str):
            reason = parsed
        else:
            name, polarity, text, margin, exact = parsed
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
            elif exact is not None:
                if log == exact:
                    continue
                reason = f"{name}: is {log[:400]!r}, expected exactly {exact!r}"
            elif (text in log) == (polarity == "+"):
                continue
            else:
                reason = f"{name}: {'missing' if polarity == '+' else 'unexpected'} {text!r}"
        print(f"EXPECT FAIL: tests/{spec.name}:{number}: {reason}", file=sys.stderr)
        ok = False
    if assertions == 0:
        print(f"EXPECT FAIL: tests/{spec.name}:1: no assertion: the file is empty or holds only blank lines and comments",
              file=sys.stderr)
        ok = False
    return ok


def compile_outputs(source):
    """The logs of the test source that a compile writes again: each log a readable line of its .expect names and
    the .out file of each of its Redirects, those that are a LOG_NAME; a name that is not one is never chosen."""
    names = set()
    expect = source.with_suffix(".expect")
    if expect.is_file():
        for _, line in assertion_lines(expect.read_text(encoding="utf-8")):
            parsed = parse_assertion(line)
            if not isinstance(parsed, str):
                names.add(parsed[0])
    names.update(f"{name}.out" for name in REDIRECT.findall(source.read_text(encoding="utf-8")))
    return [source.parent / name for name in sorted(names) if LOG_NAME.fullmatch(name)]


def run_rocq(argv):
    if len(argv) > 2 and argv[1] == "compile" and argv[-1].endswith(".v"):
        for log in compile_outputs(Path(argv[-1])):
            try:
                log.unlink()
            except FileNotFoundError:
                pass
    os.execvp(argv[0], argv)


def main(args):
    if args[:1] == ["--rocq"]:
        if len(args) < 2:
            print("check_expect.py --rocq: no Rocq command", file=sys.stderr)
            return 2
        run_rocq(args[1:])
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

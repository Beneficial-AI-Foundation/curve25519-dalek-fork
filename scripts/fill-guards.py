#!/usr/bin/env python3
"""Fill the axiom guards of a spec summary from Lean's `#print axioms` output.

Usage (from the repository root):
  scripts/fill-guards.py --strip <spec.lean>   # turn every guard into a bare `#print axioms X`
  lake env lean <spec.lean> > out.txt          # print every statement's axioms
  scripts/fill-guards.py <spec.lean> out.txt   # write the guards back

Guards have the form
  /-- [ax₁, ax₂, …] -/
  #guard_msgs (whitespace := lax, substring := true) in #print axioms X
with the list wrapped at 100 columns; a list with a single token over 100 columns gets
`set_option linter.style.longLine false in` on that command only.
"""
import re
import sys

W = 100
GUARD = "#guard_msgs (whitespace := lax, substring := true) in"


def strip(path):
    text = open(path).read()
    text = re.sub(r"(set_option linter\.style\.longLine false in\n)?(/-- \[[^\]]*\] -/\n)?"
                  r"#guard_msgs [^\n]*?in(?: |\n)#print axioms", "#print axioms", text)
    open(path, "w").write(text)


def read_messages(out):
    msgs, lines, i = {}, open(out).read().split("\n"), 0
    while i < len(lines):
        m = re.match(r"^'(.+?)' (depends on axioms: .*|does not depend on any axioms)$", lines[i])
        if m:
            block = [lines[i]]
            i += 1
            while i < len(lines) and lines[i].startswith(" "):
                block.append(lines[i])
                i += 1
            text = " ".join(" ".join(block).split())
            lst = re.search(r"(\[.*\])", text)
            msgs.setdefault(m.group(1), lst.group(1) if lst else "does not depend on any axioms")
            continue
        i += 1
    return msgs


def wrap(lst):
    if len(f"/-- {lst} -/") <= W or not lst.startswith("["):
        return [f"/-- {lst} -/"]
    items, res, cur = lst[1:-1].split(", "), [], "/-- ["
    for k, it in enumerate(items):
        piece = it + ("," if k < len(items) - 1 else "] -/")
        if len(cur) + len(piece) > W and cur != "/-- [":
            res.append(cur.rstrip())
            cur = "  "
        cur += piece + " "
    return res + [cur.rstrip()]


def fill(path, out):
    msgs, res, ns = read_messages(out), [], []
    for line in open(path).read().split("\n"):
        if (m := re.match(r"^namespace (\S+)", line)):
            ns.append(m.group(1))
        elif (m := re.match(r"^end (\S+)", line)):
            # `end A.B` closes namespaces until the components `A.B` are used up
            k = len(m.group(1).split("."))
            while k > 0 and ns:
                k -= len(ns.pop().split("."))
        if (m := re.match(r"^#print axioms (\S+)$", line)):
            full = ".".join(ns + [m.group(1)])
            if full not in msgs:
                sys.exit(f"no message for {full}")
            doc = wrap(msgs[full])
            if any(len(d) > W for d in doc):
                res.append("set_option linter.style.longLine false in")
            res += doc
            g = f"{GUARD} #print axioms {m.group(1)}"
            res += [g] if len(g) <= W else [GUARD, f"#print axioms {m.group(1)}"]
            continue
        res.append(line)
    open(path, "w").write("\n".join(res))
    print(len(msgs), "messages")


if __name__ == "__main__":
    if sys.argv[1] == "--strip":
        strip(sys.argv[2])
    else:
        fill(sys.argv[1], sys.argv[2])

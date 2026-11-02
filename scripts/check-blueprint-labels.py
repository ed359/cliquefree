#!/usr/bin/env python3
"""Check the existence blueprint's checked nodes and dependency graph."""

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--dependencies", type=Path,
        help="JSON declaration closure of Cliquefree.existenceTheorem")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    try:
        module = (root / "lean/Cliquefree/Blueprint.lean").read_text(encoding="utf-8")
        content = (root / "blueprint/src/content.tex").read_text(encoding="utf-8")
        closure = None
        if args.dependencies:
            closure = {entry["name"] for entry in json.loads(
                args.dependencies.read_text(encoding="utf-8"))}
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1

    annotated = Counter(re.findall(r'^\s*attribute\s+\[blueprint\s+"([^"]+)"', module, re.M))
    placed = Counter(re.findall(r'\\inputleannode\{([^}]*)\}', content))
    labels = set(annotated)
    errors = [
        ("annotated more than once", {v for v, n in annotated.items() if n > 1}),
        ("placed more than once", {v for v, n in placed.items() if n > 1}),
        ("annotated but never placed", labels - placed.keys()),
        ("placed but never annotated", placed.keys() - labels),
        ("defined as informal nodes", set(re.findall(r'\\label\{([^}]*)\}', content))),
        ("missing the existence target", {"thm:existence"} - labels),
    ]
    dependencies = {label: set() for label in labels}
    declarations = {}
    for block in re.split(r'(?=^\s*attribute\s+\[blueprint)', module, flags=re.M):
        match = re.search(r'\[blueprint\s+"([^"]+)"', block)
        if not match:
            continue
        label = match.group(1)
        for uses in re.findall(r'\((?:proofUses|uses)\s*:=\s*\[([^]]*)\]', block):
            dependencies[label].update(re.findall(r'"([^"]+)"', uses))
        # Each annotation ends with its declaration, before the next annotation
        # or the namespace terminator. Mathematical statements may contain \].
        body = block.split("\nend Cliquefree", 1)[0].strip()
        declarations[label] = "Cliquefree." + body.splitlines()[-1].strip()

    referenced = set().union(*dependencies.values()) if dependencies else set()
    errors.append(("referenced but undefined", referenced - labels))
    visited, active, cyclic = set(), set(), set()

    def visit(label):
        if label in active:
            cyclic.add(label)
        elif label not in visited:
            active.add(label)
            for dependency in dependencies.get(label, ()):
                visit(dependency)
            active.remove(label)
            visited.add(label)

    visit("thm:existence")
    errors.append(("outside the existence dependency graph", labels - visited))
    for label in labels:
        visit(label)
    errors.append(("in dependency cycles", cyclic))
    if closure is not None:
        errors.append(("annotating declarations outside the checked existence proof", {
            f"{label} ({declaration})" for label, declaration in declarations.items()
            if declaration not in closure
        }))
    for message, values in errors:
        if values:
            print(f"error: nodes {message}: {', '.join(sorted(values))}", file=sys.stderr)
    if any(values for _, values in errors):
        return 1

    message = (f"ok: {len(annotated)} Lean-annotated nodes; unique placements, "
               "complete acyclic dependencies, and every node leads to thm:existence")
    if closure is not None:
        message += "; every declaration belongs to its checked proof"
    print(message)
    return 0


if __name__ == "__main__":
    sys.exit(main())

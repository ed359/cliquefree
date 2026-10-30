#!/usr/bin/env python3
"""Remove deleted Cliquefree modules from a compatible doc-gen4 build cache.

Keep live module analysis and dependency documentation intact. Lake tracks edits to
existing sources; this handles deleted files, which no longer have a Lake target.
Run before ``lake build Cliquefree:docs`` to regenerate the combined index/navbar.
"""

import argparse
from pathlib import Path
import re
import sqlite3


MODULE_MARKER = re.compile(r"^(Cliquefree(?:\.[^.]+)*)\.doc(?:\..+)?$")


def is_project_module(name):
    """Only accept project module names that map to paths inside the source tree."""
    return (name == "Cliquefree" or name.startswith("Cliquefree.")) and all(
        part and "/" not in part and "\\" not in part for part in name.split(".")
    )


def cached_artifacts(build_dir):
    """Find project artifacts even when their database record is already absent."""
    artifacts = {}

    def add(module, path):
        if is_project_module(module):
            artifacts.setdefault(module, set()).add(path)

    data_dir = build_dir / "doc-data"
    if data_dir.is_dir():
        for path in data_dir.iterdir():
            if not path.is_file():
                continue
            match = MODULE_MARKER.fullmatch(path.name)
            if match:
                add(match.group(1), path)
            for prefix, suffix in (("backrefs-", ".json"), ("declaration-data-", ".bmp")):
                if path.name.startswith(prefix) and path.name.endswith(suffix):
                    add(path.name[len(prefix):-len(suffix)], path)

    doc_dir = build_dir / "doc"
    root_page = doc_dir / "Cliquefree.html"
    if root_page.is_file():
        add("Cliquefree", root_page)
    project_pages = doc_dir / "Cliquefree"
    if project_pages.is_dir():
        for path in project_pages.rglob("*.html"):
            add(".".join(path.relative_to(doc_dir).with_suffix("").parts), path)
    return artifacts


def prune_api_docs(source_root, build_dir):
    """Prune deleted module records/artifacts and return the sorted module names."""
    source_root, build_dir = Path(source_root), Path(build_dir)
    if not source_root.is_dir():
        raise ValueError(f"Lean source directory does not exist: {source_root}")

    artifacts = cached_artifacts(build_dir)
    modules = set(artifacts)
    database = build_dir / "api-docs.db"
    if database.is_file():
        with sqlite3.connect(database) as db:
            modules.update(name for (name,) in db.execute("SELECT name FROM modules")
                           if is_project_module(name))

    removed = sorted(name for name in modules
                     if not (source_root.joinpath(*name.split(".")).with_suffix(".lean")).is_file())
    if not removed:
        return []

    if database.is_file():
        with sqlite3.connect(database) as db:
            # doc-gen4's schema cascades through declarations, arguments, tactics,
            # and outgoing imports. Incoming imports are updated by Lake rebuilds.
            db.execute("PRAGMA foreign_keys = ON")
            db.executemany("DELETE FROM modules WHERE name = ?", ((name,) for name in removed))

    for name in removed:
        for path in artifacts.get(name, ()):
            path.unlink()

    # fromDb merges cached per-module search data and scans HTML for the navbar.
    # Its library target must run after deleting any module, even if it was only
    # represented by orphaned files rather than a database record.
    for path in (build_dir / "doc-data").glob("Cliquefree--library.docs_built*"):
        if path.is_file():
            path.unlink()
    return removed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=Path("lean"))
    parser.add_argument("--build-dir", type=Path, default=Path("docbuild/.lake/build"))
    args = parser.parse_args()
    try:
        removed = prune_api_docs(args.source_root, args.build_dir)
    except (OSError, sqlite3.Error, ValueError) as error:
        parser.exit(1, f"error: {error}\n")
    if removed:
        print(f"Removed {len(removed)} deleted API modules: {', '.join(removed)}")
    else:
        print("API cache has no deleted project modules.")


if __name__ == "__main__":
    main()

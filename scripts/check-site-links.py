#!/usr/bin/env python3
"""Check staged homepage targets and blueprint links against current Lean documentation."""

from html.parser import HTMLParser
import json
from pathlib import Path, PurePosixPath
import sys
from urllib.parse import unquote, urlsplit


class HTMLReferences(HTMLParser):
    def __init__(self, path):
        super().__init__(convert_charrefs=True)
        self.ids = set()
        self.hrefs = []
        self.feed(path.read_text(encoding="utf-8"))

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if attrs.get("id") is not None:
            self.ids.add(attrs["id"])
        if attrs.get("href") is not None:
            self.hrefs.append(attrs["href"])


def read_json(path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise ValueError(f"cannot read JSON from {path}: {error}") from error


def annotations(blueprint):
    result = {}
    for entry in read_json(blueprint / "module/Cliquefree/Blueprint.json"):
        if entry["type"] == "node":
            node = entry["data"]
            result[node["name"]] = node["location"]["module"]
    if not result:
        raise ValueError(f"no annotated declarations found in {blueprint}")
    return result


def check_site(site, blueprint):
    owners = annotations(blueprint)
    errors = []
    for relative in (
        "index.html",
        "blueprint.pdf",
        "blueprint/index.html",
        "blueprint/dep_graph_document.html",
        "docs/index.html",
        "docs/find/index.html",
        "docs/find/find.js",
        "docs/declaration-data.js",
    ):
        if not (site / relative).is_file():
            errors.append(f"missing staged file: {site / relative}")

    homepage = site / "index.html"
    if homepage.is_file():
        for href in HTMLReferences(homepage).hrefs:
            url = urlsplit(href)
            if url.scheme or url.netloc:
                continue
            target = (site / unquote(url.path)).resolve()
            if target.is_dir():
                target /= "index.html"
            if not target.is_relative_to(site.resolve()) or not target.is_file():
                errors.append(f"{homepage}: missing or invalid local target {href!r}")

    # Despite its extension, doc-gen4's declaration index contains JSON.
    index = site / "docs/declarations/declaration-data.bmp"
    declarations = read_json(index)["declarations"]
    if not isinstance(declarations, dict):
        raise ValueError(f"expected a declarations object in {index}")

    linked = set()
    direct_links = []
    for page in sorted((site / "blueprint").rglob("*.html")):
        for href in HTMLReferences(page).hrefs:
            url = urlsplit(href)
            path, fragment = unquote(url.path), unquote(url.fragment)
            if "/docs//" in path:
                errors.append(f"{page}: malformed documentation link {href!r}; remove the doubled slash after docs")
            if path.rstrip("/").endswith("/docs/find") and fragment.startswith("doc/"):
                linked.add(fragment.removeprefix("doc/"))
            elif "/docs/" in path and fragment.startswith("Cliquefree."):
                direct_links.append((page, href, path.rsplit("/docs/", 1)[1], fragment))

    missing = owners.keys() - linked
    if missing:
        errors.append("annotated declarations missing blueprint find links: " + ", ".join(sorted(missing)))

    pages = {}
    targets = {}
    names = owners.keys() | linked | {name for _, _, _, name in direct_links}
    docs = (site / "docs").resolve()
    for name in sorted(names):
        declaration = declarations.get(name)
        if not isinstance(declaration, dict) or not isinstance(declaration.get("docLink"), str):
            errors.append(f"{name}: missing declaration or docLink in {index}")
            continue
        url = urlsplit(declaration["docLink"])
        relative = PurePosixPath(unquote(url.path))
        anchor = unquote(url.fragment)
        target = (docs / relative).resolve()
        if url.scheme or url.netloc or url.query or not target.is_relative_to(docs):
            errors.append(f"{name}: invalid local docLink {declaration['docLink']!r}")
            continue
        targets[name] = (relative, anchor)
        if name in owners:
            expected = PurePosixPath(owners[name].replace(".", "/") + ".html")
            if relative != expected:
                errors.append(f"{name}: stale docLink module {relative}; current metadata requires {expected}")
        if anchor != name:
            errors.append(f"{name}: docLink anchor is {anchor!r}, expected the declaration name")
        if target not in pages:
            pages[target] = HTMLReferences(target).ids if target.is_file() else None
        if pages[target] is None:
            errors.append(f"{name}: documentation HTML is missing: {target}")
        elif anchor not in pages[target]:
            errors.append(f"{name}: anchor {anchor!r} is missing from {target}")

    for page, href, relative, name in direct_links:
        if name in targets and (PurePosixPath(relative), name) != targets[name]:
            errors.append(f"{page}: stale direct declaration link {href!r}; use docs/find/#doc/{name}")
    return len(owners), len(linked), errors


def main():
    if len(sys.argv) != 2:
        print(f"usage: {Path(sys.argv[0]).name} STAGED_SITE", file=sys.stderr)
        return 1
    root = Path(__file__).resolve().parent.parent
    try:
        count, links, errors = check_site(Path(sys.argv[1]), root / "lean/.lake/build/blueprint")
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    for error in errors:
        print(f"error: {error}", file=sys.stderr)
    if errors:
        return 1
    print(f"ok: homepage targets, {count} blueprint declarations, and {links} rendered find targets resolve")
    return 0


if __name__ == "__main__":
    sys.exit(main())

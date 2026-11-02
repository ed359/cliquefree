"""Check cache preservation and stale-module cleanup against doc-gen4's SQL relationships."""

import importlib.util
from pathlib import Path
import sqlite3
import tempfile
import unittest


SPEC = importlib.util.spec_from_file_location(
    "prune_api_docs", Path(__file__).parents[1] / "prune-api-docs.py"
)
PRUNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PRUNER)

# The relevant foreign keys match doc-gen4 v4.35.0's DocGen4/DB/Schema.lean.
# Include two cascade levels and the deliberately non-FK imported-module column.
SCHEMA = """
CREATE TABLE modules (name TEXT PRIMARY KEY, source_url TEXT);
CREATE TABLE module_imports (
  importer TEXT NOT NULL, imported TEXT NOT NULL,
  PRIMARY KEY (importer, imported),
  FOREIGN KEY (importer) REFERENCES modules(name) ON DELETE CASCADE
);
CREATE TABLE name_info (
  module_name TEXT NOT NULL, position INTEGER NOT NULL, name TEXT NOT NULL,
  PRIMARY KEY (module_name, position),
  FOREIGN KEY (module_name) REFERENCES modules(name) ON DELETE CASCADE
);
CREATE TABLE declaration_args (
  module_name TEXT NOT NULL, position INTEGER NOT NULL, sequence INTEGER NOT NULL,
  PRIMARY KEY (module_name, position, sequence),
  FOREIGN KEY (module_name, position)
    REFERENCES name_info(module_name, position) ON DELETE CASCADE
);
"""


class PruneApiDocsTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "lean"
        self.source.mkdir()
        self.build = self.root / "docbuild/.lake/build"
        self.build.mkdir(parents=True)
        self.database = self.build / "api-docs.db"
        with sqlite3.connect(self.database) as db:
            db.executescript(SCHEMA)

    def write(self, path, content="cached content"):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        return path

    def source_file(self, module):
        return self.write(self.source.joinpath(*module.split(".")).with_suffix(".lean"))

    def module_artifacts(self, module):
        return [self.write(self.build / "doc-data" / f"{module}{suffix}")
                for suffix in (".doc", ".doc.hash", ".doc.trace")] + [
            self.write(self.build / "doc-data" / f"backrefs-{module}.json"),
            self.write(self.build / "doc-data" / f"declaration-data-{module}.bmp"),
            self.write((self.build / "doc").joinpath(*module.split(".")).with_suffix(".html")),
        ]

    def insert_module(self, module):
        with sqlite3.connect(self.database) as db:
            db.execute("INSERT INTO modules VALUES (?, 'source')", (module,))
            db.execute("INSERT INTO name_info VALUES (?, 0, ?)", (module, f"{module}.lemma"))
            db.execute("INSERT INTO declaration_args VALUES (?, 0, 0)", (module,))

    def test_prunes_deleted_modules_and_cascades_without_touching_live_docs(self):
        live = "Cliquefree.Live"
        stale = "Cliquefree.Removed"
        dependency = "Mathlib.Dependency"
        for module in ("Cliquefree", live, stale, dependency, "CliquefreeExtra"):
            self.insert_module(module)
        self.source_file("Cliquefree")
        self.source_file(live)
        live_paths = self.module_artifacts(live)
        dependency_paths = self.module_artifacts(dependency)
        removed_paths = self.module_artifacts(stale)
        keep = live_paths + dependency_paths + [
            self.write(self.build / "doc-data/references.json"),
            self.write(self.build / "doc/references.bib"),
            self.write(self.build / "doc-data/Other--library.docs_built"),
        ]
        markers = [self.write(self.build / "doc-data" / f"Cliquefree--library.docs_built{suffix}")
                   for suffix in ("", ".hash", ".trace")]
        with sqlite3.connect(self.database) as db:
            db.executemany("INSERT INTO module_imports VALUES (?, ?)",
                           ((stale, dependency), (live, stale)))

        self.assertEqual(PRUNER.prune_api_docs(self.source, self.build), [stale])
        self.assertTrue(all(not path.exists() for path in removed_paths + markers))
        self.assertTrue(all(path.read_text() == "cached content" for path in keep))
        with sqlite3.connect(self.database) as db:
            self.assertEqual(db.execute("SELECT name FROM modules ORDER BY name").fetchall(),
                             [("Cliquefree",), (live,), ("CliquefreeExtra",), (dependency,)])
            self.assertEqual(db.execute("SELECT COUNT(*) FROM name_info WHERE module_name = ?",
                                        (stale,)).fetchone(), (0,))
            self.assertEqual(db.execute("SELECT COUNT(*) FROM declaration_args WHERE module_name = ?",
                                        (stale,)).fetchone(), (0,))
            # Incoming imports must be refreshed by the ordinary source rebuild.
            self.assertEqual(db.execute("SELECT * FROM module_imports").fetchall(), [(live, stale)])
            self.assertEqual(db.execute("PRAGMA foreign_key_check").fetchall(), [])

    def test_no_deletions_preserves_render_marker_and_is_idempotent(self):
        self.source_file("Cliquefree.Live")
        self.insert_module("Cliquefree.Live")
        paths = self.module_artifacts("Cliquefree.Live")
        paths.append(self.write(self.build / "doc-data/Cliquefree--library.docs_built"))
        before = {path: (path.read_bytes(), path.stat().st_mtime_ns) for path in paths}
        for _ in range(2):
            self.assertEqual(PRUNER.prune_api_docs(self.source, self.build), [])
        self.assertEqual(before, {path: (path.read_bytes(), path.stat().st_mtime_ns) for path in paths})

    def test_orphan_artifacts_are_removed_without_database_rows(self):
        orphan_paths = [
            self.write(self.build / "doc-data/Cliquefree.MarkerOnly.doc.trace"),
            self.write(self.build / "doc/Cliquefree/Nested/HtmlOnly.html"),
            self.write(self.build / "doc-data/backrefs-Cliquefree.BackrefsOnly.json"),
            self.write(self.build / "doc-data/declaration-data-Cliquefree.SearchOnly.bmp"),
            self.write(self.build / "doc/Cliquefree.html"),
        ]
        marker = self.write(self.build / "doc-data/Cliquefree--library.docs_built")
        self.assertEqual(PRUNER.prune_api_docs(self.source, self.build), [
            "Cliquefree", "Cliquefree.BackrefsOnly", "Cliquefree.MarkerOnly",
            "Cliquefree.Nested.HtmlOnly", "Cliquefree.SearchOnly",
        ])
        self.assertTrue(all(not path.exists() for path in orphan_paths + [marker]))
        self.assertEqual(PRUNER.prune_api_docs(self.source, self.build), [])

    def test_missing_cache_is_noop_without_creating_database(self):
        missing = self.root / "missing-cache"
        self.assertEqual(PRUNER.prune_api_docs(self.source, missing), [])
        self.assertFalse(missing.exists())

    def test_invalid_source_root_fails_before_mutating_cache(self):
        stale = self.module_artifacts("Cliquefree.Stale")
        with self.assertRaisesRegex(ValueError, "source directory does not exist"):
            PRUNER.prune_api_docs(self.root / "wrong-sources", self.build)
        self.assertTrue(all(path.exists() for path in stale))

    def test_unrelated_prefixes_and_path_like_database_names_are_preserved(self):
        names = ("CliquefreeExtra", "Cliquefree...outside", "Cliquefree./outside")
        for name in names:
            self.insert_module(name)
        self.assertEqual(PRUNER.prune_api_docs(self.source, self.build), [])
        with sqlite3.connect(self.database) as db:
            self.assertEqual({row[0] for row in db.execute("SELECT name FROM modules")}, set(names))


if __name__ == "__main__":
    unittest.main()

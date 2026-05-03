"""Manifest: the provenance graph of a ctac project.

The manifest is keyed by sha — the same content is one entry no
matter how many friendly-name aliases point at it. ``head`` and
``labels`` are kept here too so a single JSON file is enough to
reconstruct the project state (HEAD and refs files on disk are
authoritative; the manifest copies are a redundant convenience for
``prj info`` and replay).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path

from ctac.project.types import ObjectInfo, ObjectKind


SCHEMA_VERSION = 1
MANIFEST_FILENAME = "manifest.json"


@dataclass
class Manifest:
    """Mutable in-memory view of ``manifest.json``.

    ``objects`` maps sha -> ObjectInfo. ``head`` is the sha of the
    current HEAD. ``labels`` maps user-visible label -> sha.
    """

    schema_version: int = SCHEMA_VERSION
    head: str = ""
    labels: dict[str, str] = field(default_factory=dict)
    objects: dict[str, ObjectInfo] = field(default_factory=dict)

    def to_json_dict(self) -> dict:
        return {
            "schema_version": self.schema_version,
            "head": self.head,
            "labels": dict(self.labels),
            "objects": {
                sha: {
                    "kind": info.kind,
                    "parents": list(info.parents),
                    "command": info.command,
                    "args": list(info.args),
                    "names": list(info.names),
                    "created": info.created,
                    "size": info.size,
                }
                for sha, info in self.objects.items()
            },
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> "Manifest":
        sv = int(d.get("schema_version", 0))
        if sv != SCHEMA_VERSION:
            raise ValueError(
                f"unsupported project manifest schema_version {sv} "
                f"(expected {SCHEMA_VERSION})"
            )
        objects: dict[str, ObjectInfo] = {}
        for sha, raw in d.get("objects", {}).items():
            kind: ObjectKind = raw["kind"]
            objects[sha] = ObjectInfo(
                sha=sha,
                kind=kind,
                parents=tuple(raw.get("parents", ())),
                command=raw.get("command", ""),
                args=tuple(raw.get("args", ())),
                names=tuple(raw.get("names", ())),
                created=raw.get("created", ""),
                size=int(raw.get("size", 0)),
            )
        return cls(
            schema_version=sv,
            head=d.get("head", ""),
            labels=dict(d.get("labels", {})),
            objects=objects,
        )


def write_manifest(manifest: Manifest, dot_ctac: Path) -> None:
    """Atomically write ``<dot_ctac>/manifest.json``."""
    dot_ctac.mkdir(parents=True, exist_ok=True)
    target = dot_ctac / MANIFEST_FILENAME
    tmp = target.with_suffix(target.suffix + ".tmp")
    tmp.write_text(
        json.dumps(manifest.to_json_dict(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    tmp.replace(target)


def read_manifest(dot_ctac: Path) -> Manifest:
    """Read ``<dot_ctac>/manifest.json``. Raises ``FileNotFoundError`` if absent."""
    p = dot_ctac / MANIFEST_FILENAME
    if not p.is_file():
        raise FileNotFoundError(f"project manifest not found: {p}")
    return Manifest.from_json_dict(json.loads(p.read_text(encoding="utf-8")))

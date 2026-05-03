"""Append-only command log: ``.ctac/log.jsonl``.

One line per project-mutating command (``init``, ``add`` for any
HEAD-advancing or HEAD-neutral object production, ``set-head``,
``label``). The manifest is reconstructible from this log alone,
which is the design hook for ``prj replay`` (phase 4).

Schema (per line):

    {
      "ts": "2026-05-03T12:34:56Z",
      "command": "rw" | "ua" | "init" | ...,
      "args": ["--report", ...],
      "result_sha": "<sha>",       // sha of the produced object, if any
      "parents": ["<sha>", ...],   // parent shas
      "kind": "tac" | "smt" | ...,
      "name": "base.rw.tac",       // friendly-name created or reused
      "advance_head": true|false
    }
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path


LOG_FILENAME = "log.jsonl"


@dataclass(frozen=True)
class LogEntry:
    ts: str
    command: str
    args: tuple[str, ...] = field(default_factory=tuple)
    result_sha: str = ""
    parents: tuple[str, ...] = field(default_factory=tuple)
    kind: str = ""
    name: str = ""
    advance_head: bool = False

    def to_json_dict(self) -> dict:
        return {
            "ts": self.ts,
            "command": self.command,
            "args": list(self.args),
            "result_sha": self.result_sha,
            "parents": list(self.parents),
            "kind": self.kind,
            "name": self.name,
            "advance_head": self.advance_head,
        }


def append_log(dot_ctac: Path, entry: LogEntry) -> None:
    dot_ctac.mkdir(parents=True, exist_ok=True)
    p = dot_ctac / LOG_FILENAME
    line = json.dumps(entry.to_json_dict(), sort_keys=True)
    with p.open("a", encoding="utf-8") as f:
        f.write(line + "\n")


def read_log(dot_ctac: Path) -> list[LogEntry]:
    p = dot_ctac / LOG_FILENAME
    if not p.is_file():
        return []
    out: list[LogEntry] = []
    for ln in p.read_text(encoding="utf-8").splitlines():
        if not ln.strip():
            continue
        d = json.loads(ln)
        out.append(LogEntry(
            ts=d.get("ts", ""),
            command=d.get("command", ""),
            args=tuple(d.get("args", ())),
            result_sha=d.get("result_sha", ""),
            parents=tuple(d.get("parents", ())),
            kind=d.get("kind", ""),
            name=d.get("name", ""),
            advance_head=bool(d.get("advance_head", False)),
        ))
    return out

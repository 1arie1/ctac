"""Structured tracing for ctac transforms.

Provides a uniform :class:`Trace` protocol that callers can pass to
operations they want introspected. Implementations write to JSONL,
collect in memory, or no-op. Each emitted event is a JSON-serializable
dict; the trace implementation handles housekeeping (timestamps).

Designed for debugging — scalability is secondary. Pin uses this for
``--trace`` output; other transforms can adopt the same protocol.
"""

from __future__ import annotations

import json
import time
from dataclasses import dataclass, field
from typing import Protocol, TextIO, runtime_checkable


@runtime_checkable
class Trace(Protocol):
    """Structured event sink.

    Callers emit events as JSON-serializable dicts. Implementations
    augment with timestamps and route to the appropriate destination."""

    def emit(self, event: dict) -> None: ...
    def close(self) -> None: ...


class NullTrace:
    """No-op trace. Default when tracing is disabled."""

    def emit(self, event: dict) -> None:
        return None

    def close(self) -> None:
        return None


class JsonlTrace:
    """Write events as JSONL to a text stream.

    Each emitted event is augmented with a ``ts`` field (wall seconds
    since trace construction) and written as a single JSON line."""

    def __init__(self, stream: TextIO):
        self._stream = stream
        self._t0 = time.monotonic()

    def emit(self, event: dict) -> None:
        out = {**event, "ts": round(time.monotonic() - self._t0, 6)}
        self._stream.write(json.dumps(out) + "\n")

    def close(self) -> None:
        self._stream.flush()


@dataclass
class MemoryTrace:
    """Capture events in memory. Useful for tests and REPL inspection.

    Events are stored in ``events`` as a list of dicts, each carrying
    the original semantic content plus an injected ``ts`` field."""

    events: list[dict] = field(default_factory=list)
    _t0: float = field(default_factory=time.monotonic)

    def emit(self, event: dict) -> None:
        self.events.append(
            {**event, "ts": round(time.monotonic() - self._t0, 6)}
        )

    def close(self) -> None:
        return None

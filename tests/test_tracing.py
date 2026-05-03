"""Tests for ctac.tracing."""

from __future__ import annotations

import io
import json

from ctac.tracing import JsonlTrace, MemoryTrace, NullTrace, Trace


def test_null_trace_is_noop():
    t = NullTrace()
    t.emit({"event": "x"})
    t.close()
    # nothing to observe; just shouldn't raise


def test_null_trace_satisfies_protocol():
    assert isinstance(NullTrace(), Trace)


def test_jsonl_trace_writes_one_line_per_event():
    buf = io.StringIO()
    t = JsonlTrace(buf)
    t.emit({"event": "start", "x": 1})
    t.emit({"event": "stop"})
    t.close()
    lines = buf.getvalue().rstrip("\n").split("\n")
    assert len(lines) == 2
    e0, e1 = json.loads(lines[0]), json.loads(lines[1])
    assert e0["event"] == "start"
    assert e0["x"] == 1
    assert "ts" in e0
    assert e1["event"] == "stop"
    assert e1["ts"] >= e0["ts"]


def test_jsonl_trace_satisfies_protocol():
    assert isinstance(JsonlTrace(io.StringIO()), Trace)


def test_jsonl_trace_close_flushes_and_terminates_with_newline():
    buf = io.StringIO()
    t = JsonlTrace(buf)
    t.emit({"event": "only"})
    t.close()
    out = buf.getvalue()
    assert out.endswith("\n")
    assert json.loads(out.strip())["event"] == "only"


def test_memory_trace_captures_events():
    t = MemoryTrace()
    t.emit({"event": "a"})
    t.emit({"event": "b", "data": [1, 2]})
    t.close()
    assert len(t.events) == 2
    assert t.events[0]["event"] == "a"
    assert "ts" in t.events[0]
    assert t.events[1]["data"] == [1, 2]


def test_memory_trace_satisfies_protocol():
    assert isinstance(MemoryTrace(), Trace)


def test_event_dict_is_not_mutated_by_emit():
    """Caller's dict should be left untouched; trace adds ts to its copy."""
    t = MemoryTrace()
    user_event = {"event": "x"}
    t.emit(user_event)
    assert "ts" not in user_event
    assert "ts" in t.events[0]

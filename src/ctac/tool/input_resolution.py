from __future__ import annotations

import os
import re
from pathlib import Path

_EMV_DIR_RE = re.compile(r"^emv-(?P<idx>\d+)-certora.*$")


def resolve_default_certora_out_path() -> tuple[Path | None, str | None]:
    cwd = Path.cwd()
    for out_name in ("certora_out", "certrora_out"):
        root = cwd / out_name
        if not root.is_dir():
            continue
        best_idx = -1
        best_path: Path | None = None
        for ent in root.iterdir():
            if not ent.is_dir():
                continue
            m = _EMV_DIR_RE.match(ent.name)
            if not m:
                continue
            idx = int(m.group("idx"))
            if idx > best_idx or (idx == best_idx and best_path is not None and ent.name > best_path.name):
                best_idx = idx
                best_path = ent
        if best_path is not None:
            return best_path, out_name
    return None, None


def resolve_user_path(path: Path | None) -> tuple[Path, list[str]]:
    warnings: list[str] = []
    if path is not None:
        if not path.exists():
            raise ValueError(f"path does not exist: {path}")
        if not os.access(path, os.R_OK):
            raise ValueError(f"path is not readable: {path}")
        return path, warnings

    auto, out_name = resolve_default_certora_out_path()
    if auto is None:
        raise ValueError(
            "no path was provided and no certora_out/certrora_out emv-* directory was found in current directory"
        )
    warnings.append(f"path not provided; using latest emv directory from {out_name}: {auto}")
    return auto, warnings


def rule_name_from_tac_path(tac_path: Path) -> str:
    stem = tac_path.stem
    if "-" in stem:
        return stem.split("-", 1)[1]
    return stem


def resolve_tac_input_path(path: Path) -> tuple[Path, list[str]]:
    warnings: list[str] = []
    if path.is_file():
        return path, warnings
    if not path.is_dir():
        raise ValueError(f"input is neither file nor directory: {path}")

    outputs_dir = path / "outputs"
    if not outputs_dir.is_dir():
        raise ValueError(f"directory input must contain 'outputs/': {path}")

    all_tacs = sorted(p for p in outputs_dir.rglob("*.tac") if p.is_file())
    cands = [p for p in all_tacs if "-rule_not_vacuous" not in p.name]
    if not cands:
        raise ValueError(f"no non-vacuity .tac files found under: {outputs_dir}")

    preferred = sorted(p for p in cands if p.name.startswith("PresolverRule-"))
    chosen = preferred[0] if preferred else cands[0]
    if len(cands) > 1:
        warnings.append(f"multiple TAC files found under {outputs_dir}; using {chosen.name}")
    return chosen, warnings


def resolve_model_input_path(
    path: Path,
    *,
    tac_path: Path,
    kind: str,
) -> tuple[Path | None, list[str]]:
    warnings: list[str] = []
    if path.is_file():
        return path, warnings
    if not path.is_dir():
        raise ValueError(f"{kind} input is neither file nor directory: {path}")

    reports_dir = path / "Reports"
    if not reports_dir.is_dir():
        warnings.append(f"{kind} not found: expected Reports/ under {path}")
        return None, warnings

    rule = rule_name_from_tac_path(tac_path)
    prefix = f"ctpp_{rule}-"
    candidates = sorted(
        p
        for p in reports_dir.glob("ctpp_*.txt")
        if p.is_file() and p.name.startswith(prefix)
    )
    assertions = [p for p in candidates if p.name.endswith("-Assertions.txt")]

    if assertions:
        chosen = assertions[0]
        if len(assertions) > 1:
            warnings.append(
                f"multiple {kind} files match rule '{rule}' with Assertions suffix; using {chosen.name}"
            )
        return chosen, warnings

    if candidates:
        warnings.append(
            f"{kind} not found for rule '{rule}': only non-Assertions model suffixes were found; ignoring"
        )
    else:
        warnings.append(f"{kind} not found for rule '{rule}' under {reports_dir}")
    return None, warnings

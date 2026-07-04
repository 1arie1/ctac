"""Filesystem side of ``ttac lean``: locate the library, write projects.

Generated projects get a *copy* of the in-repo ``Ttac`` library so they
are self-contained and relocatable; the library's ``lean-toolchain``,
mathlib pin, and ``lake-manifest.json`` (when present) are carried over
so a generated project can never skew from the library it embeds.
"""

from __future__ import annotations

import re
import shutil
from pathlib import Path

from .encode import LeanResult

_LIB_SENTINEL = "Ttac.lean"


def locate_ttac_lib() -> Path:
    """The repo-root ``lean/`` directory holding the Ttac library."""
    lib = Path(__file__).resolve().parents[4] / "lean"
    if (lib / _LIB_SENTINEL).is_file():
        return lib
    raise FileNotFoundError(
        f"Ttac Lean library not found (expected {lib / _LIB_SENTINEL}); "
        "'ttac lean' requires a source checkout of ctac"
    )


def _mathlib_rev(lib: Path) -> str:
    text = (lib / "lakefile.toml").read_text(encoding="utf-8")
    match = re.search(r'rev\s*=\s*"([^"]+)"', text)
    if match is None:
        raise ValueError(f"no mathlib rev pin found in {lib / 'lakefile.toml'}")
    return match.group(1)


def _lakefile(module_name: str, mathlib_rev: str | None) -> str:
    lines = [
        f'name = "{module_name.lower()}"',
        'version = "0.1.0"',
        f'defaultTargets = ["{module_name}"]',
    ]
    # The Ttac library (and its mathlib dependency) is only needed by the
    # deep embedding; shallow-only projects are dependency-free core Lean.
    if mathlib_rev is not None:
        lines.extend([
            "",
            "[[require]]",
            'name = "mathlib"',
            'scope = "leanprover-community"',
            f'rev = "{mathlib_rev}"',
            "",
            "[[lean_lib]]",
            'name = "Ttac"',
        ])
    lines.extend([
        "",
        "[[lean_lib]]",
        f'name = "{module_name}"',
        "",
    ])
    return "\n".join(lines)


def _prepare_out_dir(out_dir: Path, force: bool) -> None:
    if out_dir.exists() and any(out_dir.iterdir()) and not force:
        raise FileExistsError(
            f"output directory exists and is not empty: {out_dir} "
            "(use --force to overwrite)"
        )
    out_dir.mkdir(parents=True, exist_ok=True)


def _copy_library(lib: Path, out_dir: Path, written: list[Path]) -> None:
    for name in ("lean-toolchain", "lake-manifest.json"):
        src = lib / name
        if src.is_file():
            shutil.copy2(src, out_dir / name)
            written.append(out_dir / name)
    shutil.copy2(lib / _LIB_SENTINEL, out_dir / _LIB_SENTINEL)
    written.append(out_dir / _LIB_SENTINEL)
    shutil.copytree(lib / "Ttac", out_dir / "Ttac", dirs_exist_ok=True)
    written.append(out_dir / "Ttac")


def _writer(out_dir: Path, written: list[Path]):
    def write(rel: str, text: str, *, keep_existing: bool = False) -> None:
        path = out_dir / rel
        if keep_existing and path.exists():
            return
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        written.append(path)

    return write


def write_lean_project(
    result: LeanResult, out_dir: Path, *, force: bool = False
) -> list[Path]:
    lib = locate_ttac_lib()
    _prepare_out_dir(out_dir, force)
    written: list[Path] = []
    write = _writer(out_dir, written)

    with_deep = result.deep_text is not None
    if with_deep:
        _copy_library(lib, out_dir, written)
    else:
        shutil.copy2(lib / "lean-toolchain", out_dir / "lean-toolchain")
        written.append(out_dir / "lean-toolchain")

    write(
        "lakefile.toml",
        _lakefile(result.module_name, _mathlib_rev(lib) if with_deep else None),
    )
    write(f"{result.module_name}.lean", result.root_text)
    if result.deep_text is not None:
        write(f"{result.module_name}/Deep.lean", result.deep_text)
    if result.shallow_text is not None:
        write(f"{result.module_name}/Shallow.lean", result.shallow_text)
    write(f"{result.module_name}/Proofs.lean", result.proofs_text, keep_existing=True)
    return written


def write_vc_check_project(
    result, out_dir: Path, *, force: bool = False
) -> list[Path]:
    """Write a `ttac vc-check` project. Every file is regenerated -
    this is a checker artifact, not a proof workspace."""
    lib = locate_ttac_lib()
    _prepare_out_dir(out_dir, force)
    written: list[Path] = []
    write = _writer(out_dir, written)

    _copy_library(lib, out_dir, written)
    write("lakefile.toml", _lakefile(result.module_name, _mathlib_rev(lib)))
    write(f"{result.module_name}.lean", result.root_text)
    write(f"{result.module_name}/Deep.lean", result.deep_text)
    write(f"{result.module_name}/Vc.lean", result.vc_text)
    write(f"{result.module_name}/Check.lean", result.check_text)
    return written

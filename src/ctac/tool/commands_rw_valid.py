"""`ctac rw-valid` — emit per-rule SMT soundness scripts.

Writes one ``.smt2`` per registered :class:`ValidationCase` into the
output directory, plus a ``manifest.json`` listing each case's
expected outcome and a short description. Running a solver on each
script and expecting ``unsat`` is the soundness check; this command
does not run the solver itself — users iterate with ``z3``, custom
tactics, or Lean.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.rewrite.rules import all_rule_names, validation_cases
from ctac.tool.cli_runtime import PLAIN_HELP, agent_option, app, console, plain_requested


@app.command("rw-valid")
def rw_valid_cmd(
    output_dir: Annotated[
        Path,
        typer.Option(
            "--output-dir",
            "-o",
            help="Directory to write *.smt2 + manifest.json.",
        ),
    ] = ...,  # type: ignore[assignment]
    rule: Annotated[
        Optional[list[str]],
        typer.Option(
            "--rule",
            help="Only emit scripts for this rule (repeatable).",
        ),
    ] = None,
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
) -> None:
    """Emit SMT-LIB soundness scripts for rewrite rules with declared specs.

    Each script is a self-contained SMT-LIB 2 instance whose expected
    outcome is ``unsat`` (the rule is sound). Run any SMT-LIB 2 solver
    on the output files — ``ctac`` does not run z3 automatically.
    """
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)

    output_dir.mkdir(parents=True, exist_ok=True)

    wanted: set[str] | None = {r for r in rule} if rule else None
    selected = [
        vc for vc in validation_cases if wanted is None or vc.name in wanted
    ]

    if not selected:
        if wanted:
            msg = f"no validation cases match --rule {sorted(wanted)!r}"
        else:
            msg = "no validation cases registered"
        c.print(f"rw-valid: {msg}" if plain else f"[red]rw-valid:[/red] {msg}")
        raise typer.Exit(1)

    manifest_rules = []
    covered_rule_names: set[str] = set()

    if plain:
        c.print("rw-valid:")
    else:
        c.print("[bold]rw-valid[/bold]:")

    for vc in selected:
        file_path = output_dir / f"{vc.file_stem}.smt2"
        file_path.write_text(vc.smt2_text, encoding="utf-8")
        covered_rule_names.add(vc.name)
        display_name = vc.name if not vc.case else f"{vc.name}.{vc.case}"
        if plain:
            c.print(f"  {display_name}: wrote {file_path}")
        else:
            c.print(f"  [cyan]{display_name}[/cyan]: wrote [bold]{file_path}[/bold]")
        manifest_rules.append(
            {
                "rule": vc.name,
                "case": vc.case,
                "smt2": f"{vc.file_stem}.smt2",
                "expected": vc.expected,
                "description": vc.description,
            }
        )

    missing = sorted(
        r for r in all_rule_names if r not in covered_rule_names and wanted is None
    )
    manifest = {
        "rules": manifest_rules,
        "missing": missing,
    }
    manifest_path = output_dir / "manifest.json"
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    if plain:
        c.print(f"  manifest: wrote {manifest_path}")
    else:
        c.print(f"  [cyan]manifest[/cyan]: wrote [bold]{manifest_path}[/bold]")

    rules_covered = len(covered_rule_names)
    total = len(manifest_rules)
    suffix = ""
    if missing:
        suffix = f"; no spec for: {', '.join(missing)}"
    if plain:
        c.print(f"  total: {total} scripts, {rules_covered} rule(s) covered{suffix}")
    else:
        c.print(
            f"  [bold]total[/bold]: {total} scripts, {rules_covered} rule(s) covered{suffix}"
        )

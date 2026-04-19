from __future__ import annotations

from ctac.smt.model import SmtScript


def render_smt_script(script: SmtScript) -> str:
    lines: list[str] = []
    if script.unsat_core:
        lines.append("(set-option :produce-unsat-cores true)")
        lines.append("(set-option :smt.core.minimize true)")
    for comment in script.comments:
        lines.append(f"; {comment}")
    lines.append(f"(set-logic {script.logic})")
    for decl in script.declarations:
        lines.append(f"(declare-const {decl.name} {decl.sort})")
    lines.extend(script.assertions)
    if script.check_sat:
        lines.append("(check-sat)")
        if script.unsat_core:
            lines.append("(get-unsat-core)")
    return "\n".join(lines) + "\n"

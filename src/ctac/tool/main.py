from importlib import import_module

from ctac.ast.run_format import pp_terminator_line as _pp_terminator_line
from ctac.ast.run_format import source_prefix_for_cmd as _source_prefix_for_cmd
from ctac.tool.cli_runtime import app
from ctac.tool.commands_diff import truncate_diff_lines as _truncate_diff_lines

# Import subcommand modules for Typer registration side effects.
import_module("ctac.tool.commands_absint")
import_module("ctac.tool.commands_cfg_pp_search")
import_module("ctac.tool.commands_df")
import_module("ctac.tool.commands_diff")
import_module("ctac.tool.commands_op_diff")
import_module("ctac.tool.commands_pin")
import_module("ctac.tool.commands_run")
import_module("ctac.tool.commands_rw")
import_module("ctac.tool.commands_rw_eq")
import_module("ctac.tool.commands_rw_valid")
import_module("ctac.tool.commands_slice")
import_module("ctac.tool.commands_smt")
import_module("ctac.tool.commands_splitcrit")
import_module("ctac.tool.commands_stats")
import_module("ctac.tool.commands_types")
import_module("ctac.tool.commands_ua")

__all__ = [
    "main",
    "_pp_terminator_line",
    "_source_prefix_for_cmd",
    "_truncate_diff_lines",
]


def main() -> None:
    app()


if __name__ == "__main__":
    main()

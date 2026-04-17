"""Parse Certora `.tac` dump files."""

from ctac.parse.tac_file import ParseError, parse_path, parse_string

__all__ = ["ParseError", "parse_path", "parse_string"]

"""Gamma-placement prep primitives.

Task 1: ``ControlDependenceResult`` exposes per-block controllers in
reverse-topological order plus a topo index.
Task 2: ``branch_conditions`` is the controller-keyed branch-condition
accessor that wires the same condition symbol into the gamma gate and
the CFG-constraint layer.
"""

from __future__ import annotations

from ctac.analysis import analyze_control_dependence
from ctac.parse import parse_string
from ctac.smt.encoding.path_skeleton import branch_conditions


# Two independent branches (e on c1, a on c2, b on c3) both reach the
# merge block n while each can also bypass it (a->x, b->y). So n is
# directly control-dependent on BOTH a and b; x on a, y on b; a and b
# on e. Single common exit z.
_NESTED = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tc1:bool
\tc2:bool
\tc3:bool
\tR0:bv256
}
Program {
\tBlock e Succ [a, b] {
\t\tAssignHavocCmd c1
\t\tJumpiCmd a b c1
\t}
\tBlock a Succ [n, x] {
\t\tAssignHavocCmd c2
\t\tJumpiCmd n x c2
\t}
\tBlock b Succ [n, y] {
\t\tAssignHavocCmd c3
\t\tJumpiCmd n y c3
\t}
\tBlock n Succ [z] {
\t\tAssignExpCmd R0 0x1
\t\tJumpCmd z
\t}
\tBlock x Succ [z] {
\t\tJumpCmd z
\t}
\tBlock y Succ [z] {
\t\tJumpCmd z
\t}
\tBlock z Succ [] {
\t\tAssertCmd c1 "ok"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _program():
    return parse_string(_NESTED).program


def test_controllers_direct_dependences() -> None:
    cd = analyze_control_dependence(_program())
    assert set(cd.controllers["n"]) == {"a", "b"}
    assert cd.controllers["a"] == ("e",)
    assert cd.controllers["b"] == ("e",)
    assert cd.controllers["x"] == ("a",)
    assert cd.controllers["y"] == ("b",)
    # entry and the post-dominating merge/exit depend on nothing.
    assert cd.controllers["e"] == ()
    assert cd.controllers["z"] == ()


def test_controllers_sorted_reverse_topo() -> None:
    cd = analyze_control_dependence(_program())
    # n's two controllers come back closest-to-merge first: b after a in
    # execution order, so b (higher topo index) leads.
    assert cd.controllers["n"] == ("b", "a")
    # General invariant: every controller list is non-increasing in topo
    # index (reverse-topological).
    for deps in cd.controllers.values():
        idxs = [cd.topo_index[d] for d in deps]
        assert idxs == sorted(idxs, reverse=True)


def test_topo_index_respects_execution_order() -> None:
    cd = analyze_control_dependence(_program())
    assert cd.topo_index["e"] == 0
    # controllers precede the blocks they control.
    assert cd.topo_index["a"] < cd.topo_index["n"]
    assert cd.topo_index["b"] < cd.topo_index["n"]
    assert cd.topo_index["e"] < cd.topo_index["a"]


def test_branch_conditions_keyed_by_controller() -> None:
    bcs = branch_conditions(_program(), symbol_term_by_name={})
    # only the conditional-terminator blocks appear.
    assert set(bcs) == {"e", "a", "b"}
    assert bcs["e"].then_target == "a"
    assert bcs["e"].else_target == "b"
    assert bcs["e"].cond == "c1"
    assert bcs["a"].cond == "c2"
    assert bcs["b"].cond == "c3"


def test_branch_conditions_uses_symbol_term_map() -> None:
    # The same map the encoder uses to name condition symbols, so the
    # gamma gate references exactly the CFG-constraint symbol.
    bcs = branch_conditions(_program(), symbol_term_by_name={"c1": "BR_c1"})
    assert bcs["e"].cond == "BR_c1"
    # symbols absent from the map fall back to the sanitized name.
    assert bcs["a"].cond == "c2"

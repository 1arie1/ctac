TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
		safe_math_narrow_bv256:JSON{"x":1}
	}
	UninterpretedFunctions {
	}
	R_num:bv256
	R_den:bv256
	R_floor:bv256
	I_prod:bv256
	R_prod:bv256
	R_trunc:bv256
	R_high:bv256
	X1:bv256
	X2:bv256
	R_ceil:bv256
	S:bool
}
Program {
	Block e Succ [] {
		AssignHavocCmd R_num
		AssumeExpCmd LAnd(Ge(R_num 0x0) Le(R_num 0xffffffff))
		AssignHavocCmd R_den
		AssumeExpCmd LAnd(Ge(R_den 0x1) Le(R_den 0xffff))
		AssignExpCmd R_floor Apply(safe_math_narrow_bv256:bif IntDiv(R_num R_den))
		AssignExpCmd I_prod IntMul(R_floor R_den)
		AssignExpCmd R_prod Apply(safe_math_narrow_bv256:bif I_prod)
		AssignExpCmd R_trunc BWAnd(R_prod 0xffffffffffffffff)
		AssignExpCmd R_high Sub(0x0 ShiftRightLogical(R_prod 0x40))
		AssignExpCmd X1 Sub(R_high Ite(Lt(R_num R_trunc) 0x1 0x0))
		AssignExpCmd X2 Sub(R_num R_trunc)
		AssignExpCmd R_ceil Apply(safe_math_narrow_bv256:bif IntAdd(R_floor Ite(LAnd(Eq(X2 0x0) Eq(X1 0x0)) 0x0 0x1)))
		AssignExpCmd S Le(R_ceil 0xffffff)
		AssertCmd S "R6 stress: ceiling-division chain — the most complex rewrite, replaces 6-cmd chain with havoc + algebraic bounds. Most worrying for soundness."
	}
}
Axioms {
}
Metas {
  "0": []
}

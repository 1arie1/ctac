TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
		safe_math_narrow_bv256:JSON{"x":1}
	}
	UninterpretedFunctions {
	}
	R0:bv256
	R1:bv256
	R2:bv256
	R3:bv256
	R4:bv256
	S:bool
}
Program {
	Block entry Succ [] {
		AssignHavocCmd R0
		AssumeExpCmd Le(R0 0xffffffff)
		AssignExpCmd R1 IntMul(0x4000(int) R0)
		AssignExpCmd R2 Apply(safe_math_narrow_bv256:bif R1)
		AssignExpCmd R3 BWAnd(R2 0x3fffffffc000)
		AssignExpCmd S Eq(R3 R2)
		AssertCmd S "R1 stress: keep_bits should equal R2 since R2 has zero low bits"
	}
}
Axioms {
}
Metas {
  "0": []
}

TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	A:bv256
	R:bv256
	S:bool
}
Program {
	Block entry Succ [] {
		AssignHavocCmd A
		AssumeExpCmd Le(A 0xff)
		AssignExpCmd R Div(IntMul(0x4(int) A) 0x4)
		AssignExpCmd S Le(R 0xff)
		AssertCmd S "R3 stress: Div(Mul(c,A),c) = A"
	}
}
Axioms {
}
Metas {
  "0": []
}

TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	A:bv256
	B:bv256
	R:bv256
	S:bool
}
Program {
	Block entry Succ [] {
		AssignHavocCmd A
		AssignHavocCmd B
		AssumeExpCmd Le(A 0xff)
		AssumeExpCmd Le(B 0xff)
		AssignExpCmd R Mul(A B)
		AssignExpCmd S Le(R 0xffff)
		AssertCmd S "MUL_BV_TO_INT stress: small operands, product fits in bv256"
	}
}
Axioms {
}
Metas {
  "0": []
}

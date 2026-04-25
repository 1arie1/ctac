TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	A:bv256
	R:bv256
	B:bv256
	S:bool
}
Program {
	Block entry Succ [] {
		AssignHavocCmd A
		AssignHavocCmd B
		AssumeExpCmd Le(A 0xff)
		AssignExpCmd R Mul(Mod(Div(A 0x10) 0x10) 0x10)
		AssignExpCmd S Eq(R B)
		AssertCmd S "R1 stress: unsound input — A directly bounded, low bits not zero"
	}
}
Axioms {
}
Metas {
  "0": []
}

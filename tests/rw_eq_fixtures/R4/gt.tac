TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	A:bv256
	S:bool
}
Program {
	Block entry Succ [] {
		AssignHavocCmd A
		AssumeExpCmd Le(A 0xffff)
		AssignExpCmd S Gt(Div(A 0x10) 0xff)
		AssertCmd S "R4 stress (Gt): Gt(Div(A,16), 255) <-> Ge(A, 16*256)"
	}
}
Axioms {
}
Metas {
  "0": []
}

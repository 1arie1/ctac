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
		AssignExpCmd S Ge(Div(A 0x10) 0xff)
		AssertCmd S "R4 stress (Ge): Ge(Div(A,16), 255) <-> Ge(A, 16*255)"
	}
}
Axioms {
}
Metas {
  "0": []
}

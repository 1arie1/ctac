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
		AssignExpCmd S Eq(Div(A 0x10) 0x5)
		AssertCmd S "R4 stress (Eq): Eq(Div(A,16), 5) <-> A in [80, 95]"
	}
}
Axioms {
}
Metas {
  "0": []
}

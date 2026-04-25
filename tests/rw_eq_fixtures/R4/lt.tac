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
		AssignExpCmd S Lt(Div(A 0x10) 0xff)
		AssertCmd S "R4 stress (Lt): Lt(Div(A,16), 255) <-> Lt(A, 16*255)"
	}
}
Axioms {
}
Metas {
  "0": []
}

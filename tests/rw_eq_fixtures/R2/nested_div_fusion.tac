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
		AssumeExpCmd Le(A 0xffff)
		AssignExpCmd R Div(Div(A 0x4) 0x8)
		AssignExpCmd S Le(R 0x100)
		AssertCmd S "R2 stress: Div(Div(A,4),8) = Div(A,32)"
	}
}
Axioms {
}
Metas {
  "0": []
}

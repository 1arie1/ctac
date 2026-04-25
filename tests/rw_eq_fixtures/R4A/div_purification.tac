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
		AssumeExpCmd Gt(B 0x0)
		AssumeExpCmd Le(A 0xffff)
		AssumeExpCmd Le(B 0xff)
		AssignExpCmd R Div(A B)
		AssignExpCmd S Le(R 0xffff)
		AssertCmd S "R4A stress: Div(A,B) -> havoc R; assume B*R<=A; assume A<B*(R+1)"
	}
}
Axioms {
}
Metas {
  "0": []
}

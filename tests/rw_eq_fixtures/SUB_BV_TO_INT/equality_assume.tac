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
		AssumeExpCmd Eq(A B)
		AssignExpCmd R Sub(A B)
		AssignExpCmd S Eq(R 0x0)
		AssertCmd S "SUB_BV_TO_INT stress: A == B forces Sub(A,B) == 0"
	}
}
Axioms {
}
Metas {
  "0": []
}

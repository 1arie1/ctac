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
		AssignExpCmd R Ite(Lt(A 0x100) 0x1 0x2)
		AssignExpCmd S Eq(R 0x1)
		AssertCmd S "ITE_COND_FOLD stress: Lt(A, 256) is always true given Le(A, 0xff)"
	}
}
Axioms {
}
Metas {
  "0": []
}

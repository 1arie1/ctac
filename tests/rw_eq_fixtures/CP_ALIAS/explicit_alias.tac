TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	A:bv256
	X:bv256
	Y:bv256
	S:bool
}
Program {
	Block entry Succ [] {
		AssignHavocCmd A
		AssumeExpCmd Le(A 0xff)
		AssignExpCmd X Add(A 0x5)
		AssignExpCmd Y X
		AssignExpCmd S Eq(Y A)
		AssertCmd S "CP_ALIAS stress: Y = X (alias) — CP propagates X to use, DCE removes Y."
	}
}
Axioms {
}
Metas {
  "0": []
}

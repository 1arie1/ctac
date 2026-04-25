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
		AssignExpCmd Y Add(A 0x5)
		AssignExpCmd S Eq(X Y)
		AssertCmd S "CSE stress: two identical RHSes — Y becomes alias for X, then DCE'd. rw-eq must catch the resulting variable removal via rule 9b."
	}
}
Axioms {
}
Metas {
  "0": []
}

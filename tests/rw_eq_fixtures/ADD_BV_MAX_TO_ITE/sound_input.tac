TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	X:bv256
	R:bv256
	S:bool
}
Program {
	Block entry Succ [] {
		AssignHavocCmd X
		AssignExpCmd R Add(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff X)
		AssignExpCmd S Eq(R 0x0)
		AssertCmd S "ADD_BV_MAX_TO_ITE stress: R = BV256_MAX + X"
	}
}
Axioms {
}
Metas {
  "0": []
}

TACSymbolTable {
		UninterpSort skey
		safe_math_narrow_bv256:JSON{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow.Implicit","returnSort":{"bits":256}}
	R24:bv256
	R26:bv256
	R32:bv256
	R33:bv256
	R44:bv256
	R47:bv256
	R48:bv256
	R51:bv256
	R53:bv256
	R55:bv256
	I164:int
	I170:int
	B36:bool
	R171:bv256
	R178:bv256
	R179:bv256
	R182:bv256
	I37:int
	I43:int
	B183:bool
	R9:bv256
}
Program {
	Block 0_0_0_0_0_0 Succ [40_1_0_0_0_0, 43_1_0_0_0_0] {
		AssignHavocCmd:7 R9
		AssignHavocCmd R24
		AssignHavocCmd:24 R26
		AssignHavocCmd:28 R32
		AssignHavocCmd:29 R33
		AssumeExpCmd LAnd(Ge(R33 0x1 ) Le(R33 0x3ffffffffffff ) )
		AssignExpCmd:34 B36 Eq(R26:17 R32 )
		JumpiCmd:34 43_1_0_0_0_0 40_1_0_0_0_0 B36
	}
	Block 28_1_0_0_0_0 Succ [29_1_0_0_0_0] {
		AssignExpCmd:41 I37 IntMul(R24:17 R33:17)
		AssignExpCmd:42 I43 IntDiv(Apply(safe_math_narrow_bv256:bif I37:17) R26:17 )
		AssumeExpCmd LAnd(Ge(I43 0x0(int) ) Le(I43 0xffffffffffffffff(int) ) )
		AssignExpCmd:42 R44 Apply(safe_math_narrow_bv256:bif I43)
		AssignExpCmd R47 R44
	}
	Block 29_1_0_0_0_0 Succ [] {
		AssignExpCmd:47 R48 BWAnd(R47 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000 )
		AssignExpCmd R51 Ite(Eq(R48 0x0 ) 0x0 ShiftRightLogical(R47:17 0xe ) )
		AssignExpCmd R53 Ite(Lt(R9 R51 ) R9 R51 )
		AssumeExpCmd Le(R53 0xffffffff )
		AssignExpCmd R55 Ite(Lt(R9 R182 ) R9 R182 )
		AssumeExpCmd Le(R55 0xffffffff )
		AssumeExpCmd Eq(R55 R53 )
		AssumeExpCmd false
	}
	Block 31_1_0_0_0_0 Succ [29_1_0_0_0_0] {
		AssignExpCmd R47 R24:17
		AssumeExpCmd false
	}
	Block 40_1_0_0_0_0 Succ [41_1_0_0_0_0] {
		AssignExpCmd:41 I164 IntMul(R24:17 R32)
		AssignExpCmd:42 I170 IntDiv(Apply(safe_math_narrow_bv256:bif I164) R26:17 )
		AssumeExpCmd LAnd(Ge(I170 0x0(int) ) Le(I170 0xffffffffffffffff(int) ) )
		AssignExpCmd:42 R171 Apply(safe_math_narrow_bv256:bif I170)
		AssignExpCmd R178 R171
	}
	Block 41_1_0_0_0_0 Succ [28_1_0_0_0_0, 31_1_0_0_0_0] {
		AssignExpCmd:47 R179 BWAnd(R178 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000 )
		AssignExpCmd R182 Ite(Eq(R179 0x0 ) 0x0 ShiftRightLogical(R178:17 0xe ) )
		AssignExpCmd:34 B183 Eq(R26:17 R33:17 )
		JumpiCmd:34 31_1_0_0_0_0 28_1_0_0_0_0 B183
	}
	Block 43_1_0_0_0_0 Succ [41_1_0_0_0_0] {
		AssignExpCmd R178 R24:17
		AssumeExpCmd false
	}
}
Axioms {
}
Metas {
}

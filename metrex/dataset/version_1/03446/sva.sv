// SVA for my_and_nor
// Drop inside the module or bind to it. Uses @(*) sampling.
`ifndef SYNTHESIS
// Structural equivalence of internal nets
a_b_inv:     assert property (@(*) b          === ~B1_N);
a_and_eq:    assert property (@(*) and0_out   === (A1 & A2));
a_nor_eq:    assert property (@(*) nor0_out_Y === ~(b | and0_out));
a_buf_eq:    assert property (@(*) Y          === nor0_out_Y);

// Functional equivalence (when inputs are known)
a_func_known: assert property (@(*) !$isunknown({A1,A2,B1_N}) |-> (Y === (B1_N & (~A1 | ~A2))));
a_no_x_out:   assert property (@(*) !$isunknown({A1,A2,B1_N}) |-> !$isunknown(Y));

// Deterministic cases with partial-X on inputs
a_det_B0:     assert property (@(*) (B1_N === 1'b0)                                       |-> (Y === 1'b0));
a_det_any0:   assert property (@(*) (B1_N === 1'b1 && (A1 === 1'b0 || A2 === 1'b0))       |-> (Y === 1'b1));
a_det_all1:   assert property (@(*) (B1_N === 1'b1 && A1 === 1'b1 && A2 === 1'b1)         |-> (Y === 1'b0));

// Truth-table coverage (8 combos) with expected Y
cover property (@(*) (B1_N===0 && A1===0 && A2===0 && Y===0));
cover property (@(*) (B1_N===0 && A1===0 && A2===1 && Y===0));
cover property (@(*) (B1_N===0 && A1===1 && A2===0 && Y===0));
cover property (@(*) (B1_N===0 && A1===1 && A2===1 && Y===0));
cover property (@(*) (B1_N===1 && A1===0 && A2===0 && Y===1));
cover property (@(*) (B1_N===1 && A1===0 && A2===1 && Y===1));
cover property (@(*) (B1_N===1 && A1===1 && A2===0 && Y===1));
cover property (@(*) (B1_N===1 && A1===1 && A2===1 && Y===0));

// Output toggle coverage
cover property (@(*) $rose(Y));
cover property (@(*) $fell(Y));
`endif
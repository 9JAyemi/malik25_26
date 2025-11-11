// SVA for sky130_fd_sc_ls__nor4bb
// Function: Y = (~(A | B)) & C_N & D_N  == (!A & !B & C_N & D_N)

bind sky130_fd_sc_ls__nor4bb sky130_fd_sc_ls__nor4bb_sva i_nor4bb_sva (.*);

module sky130_fd_sc_ls__nor4bb_sva (
  input logic Y, A, B, C_N, D_N
);

  // Functional equivalence (4-state, sampled after zero-delay to allow propagation)
  property p_func;
    @(A or B or C_N or D_N or Y)
      1'b1 |-> ##0 (Y === ((~(A | B)) & C_N & D_N));
  endproperty
  assert property (p_func);

  // Controlling values force-low
  property p_force_low;
    @(A or B or C_N or D_N or Y)
      ((A === 1'b1) || (B === 1'b1) || (C_N === 1'b0) || (D_N === 1'b0))
      |-> ##0 (Y === 1'b0);
  endproperty
  assert property (p_force_low);

  // Necessity for Y==1
  property p_y_high_requires_inputs;
    @(A or B or C_N or D_N or Y)
      (Y === 1'b1) |-> ##0 ((A === 1'b0) && (B === 1'b0) && (C_N === 1'b1) && (D_N === 1'b1));
  endproperty
  assert property (p_y_high_requires_inputs);

  // Basic coverage
  cover property (@(A or B or C_N or D_N or Y) ##0 (Y === 1'b1));
  cover property (@(A or B or C_N or D_N or Y) $rose(Y));
  cover property (@(A or B or C_N or D_N or Y) $fell(Y));

  // Exhaustive input combination coverage (16 combos)
  genvar i;
  for (i = 0; i < 16; i++) begin : gen_combo_cov
    localparam logic [3:0] V = i[3:0];
    cover property (@(A or B or C_N or D_N or Y) ##0 ({A, B, C_N, D_N} === V));
  end

endmodule
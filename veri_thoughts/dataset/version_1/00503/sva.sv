// SVA for sky130_fd_sc_hd__and4
module sky130_fd_sc_hd__and4_sva (
  input logic A, B, C, D,
  input logic X,
  input logic and0_out_X
);

  // Buffer correctness (internal connectivity)
  property p_buf_eq; @(*) 1'b1 |-> ##0 (X === and0_out_X); endproperty
  assert property (p_buf_eq);

  // Functional correctness when inputs are known
  property p_func_known; @(*) (!$isunknown({A,B,C,D})) |-> ##0 (X === (A & B & C & D)); endproperty
  assert property (p_func_known);

  // Any input 0 forces X=0 (even with X/Z on other inputs)
  property p_any_zero_forces_zero; @(*)
    ((A===1'b0) || (B===1'b0) || (C===1'b0) || (D===1'b0)) |-> ##0 (X===1'b0);
  endproperty
  assert property (p_any_zero_forces_zero);

  // All inputs 1 forces X=1
  property p_all_ones_forces_one; @(*) (A===1 && B===1 && C===1 && D===1) |-> ##0 (X===1); endproperty
  assert property (p_all_ones_forces_one);

  // If X is 1, all inputs must be 1
  property p_x_high_implies_inputs_high; @(*) (X===1) |-> ##0 (A===1 && B===1 && C===1 && D===1); endproperty
  assert property (p_x_high_implies_inputs_high);

  // Full input-space coverage (all 16 combinations)
  genvar i;
  generate
    for (i=0; i<16; i++) begin : cov_in_patterns
      localparam int unsigned VI = i;
      cover property (@(*) ##0 ({A,B,C,D} === VI[3:0]));
    end
  endgenerate

  // Cover output high and low
  cover property (@(*) ##0 (X===1'b1));
  cover property (@(*) ##0 (X===1'b0));

endmodule

// Bind SVA to the DUT (accesses internal and0_out_X)
bind sky130_fd_sc_hd__and4 sky130_fd_sc_hd__and4_sva u_and4_sva (
  .A(A), .B(B), .C(C), .D(D), .X(X), .and0_out_X(and0_out_X)
);
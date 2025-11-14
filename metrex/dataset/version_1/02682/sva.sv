// SVA for sky130_fd_sc_hvl__nor2
// Concise, functionally complete, with key coverage.
// Bind into the DUT to also check the internal buffer tap.

module sky130_fd_sc_hvl__nor2_sva (
  input logic A,
  input logic B,
  input logic Y,
  input logic nor0_out_Y
);
  default clocking cb @(posedge $global_clock); endclocking

  // Functional correctness when inputs are known
  property p_func;
    !$isunknown({A,B}) |-> (Y === ~(A | B));
  endproperty
  assert property (p_func);

  // Buffer must preserve NOR output (no inversion, no corruption) when inputs are known
  property p_buf_consistency;
    !$isunknown({A,B}) |-> (Y === nor0_out_Y);
  endproperty
  assert property (p_buf_consistency);

  // Basic truth-table coverage
  cover property (A==0 && B==0 && Y==1);
  cover property (A==0 && B==1 && Y==0);
  cover property (A==1 && B==0 && Y==0);
  cover property (A==1 && B==1 && Y==0);

  // Edge coverage on inputs and output
  cover property ($rose(A));  cover property ($fell(A));
  cover property ($rose(B));  cover property ($fell(B));
  cover property ($rose(Y));  cover property ($fell(Y));
endmodule

bind sky130_fd_sc_hvl__nor2 sky130_fd_sc_hvl__nor2_sva sva_i (
  .A(A),
  .B(B),
  .Y(Y),
  .nor0_out_Y(nor0_out_Y)
);
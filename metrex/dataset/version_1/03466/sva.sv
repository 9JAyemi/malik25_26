// SVA for sky130_fd_sc_hd__a221o: X = (A1 & A2) | (B1 & B2) | C1
// Bind this checker to the DUT to verify function, X-prop, and provide compact full coverage.

module sky130_fd_sc_hd__a221o_sva;

  // Sample on any input edge
  default clocking cb @(
      posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge B1 or negedge B1 or
      posedge B2 or negedge B2 or
      posedge C1 or negedge C1
  ); endclocking

  // Power rails tied correctly
  a_power: assert property (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0);

  // Functional equivalence when inputs are known
  a_func: assert property (
    !$isunknown({A1,A2,B1,B2,C1}) |->
      (X == ((A1 & A2) | (B1 & B2) | C1))
  );

  // No X/Z on outputs (and key internal nets) when inputs are known
  a_no_x_out: assert property (!$isunknown({A1,A2,B1,B2,C1}) |-> !$isunknown(X));
  a_no_x_and0: assert property (!$isunknown({B1,B2}) |-> !$isunknown(and0_out));
  a_no_x_and1: assert property (!$isunknown({A1,A2}) |-> !$isunknown(and1_out));
  a_no_x_or0:  assert property (!$isunknown({A1,A2,B1,B2,C1}) |-> !$isunknown(or0_out_X));

  // Gate-level decomposition checks (guarded by knowns)
  a_and0: assert property (!$isunknown({B1,B2}) |-> (and0_out == (B1 & B2)));
  a_and1: assert property (!$isunknown({A1,A2}) |-> (and1_out == (A1 & A2)));
  a_or0:  assert property (!$isunknown({A1,A2,B1,B2,C1}) |-> (or0_out_X == (and1_out | and0_out | C1)));
  a_buf0: assert property (X == or0_out_X);

  // Compact full functional coverage over the three OR terms: {A1&A2, B1&B2, C1}
  // Each cover ensures X matches the expected value for that minterm combination.
  c_m000: cover property (!$isunknown({A1,A2,B1,B2,C1}) &&
                          {(A1&A2),(B1&B2),C1} == 3'b000 && X==1'b0);
  c_m001: cover property (!$isunknown({A1,A2,B1,B2,C1}) &&
                          {(A1&A2),(B1&B2),C1} == 3'b001 && X==1'b1);
  c_m010: cover property (!$isunknown({A1,A2,B1,B2,C1}) &&
                          {(A1&A2),(B1&B2),C1} == 3'b010 && X==1'b1);
  c_m011: cover property (!$isunknown({A1,A2,B1,B2,C1}) &&
                          {(A1&A2),(B1&B2),C1} == 3'b011 && X==1'b1);
  c_m100: cover property (!$isunknown({A1,A2,B1,B2,C1}) &&
                          {(A1&A2),(B1&B2),C1} == 3'b100 && X==1'b1);
  c_m101: cover property (!$isunknown({A1,A2,B1,B2,C1}) &&
                          {(A1&A2),(B1&B2),C1} == 3'b101 && X==1'b1);
  c_m110: cover property (!$isunknown({A1,A2,B1,B2,C1}) &&
                          {(A1&A2),(B1&B2),C1} == 3'b110 && X==1'b1);
  c_m111: cover property (!$isunknown({A1,A2,B1,B2,C1}) &&
                          {(A1&A2),(B1&B2),C1} == 3'b111 && X==1'b1);

endmodule

bind sky130_fd_sc_hd__a221o sky130_fd_sc_hd__a221o_sva sva_a221o_i;
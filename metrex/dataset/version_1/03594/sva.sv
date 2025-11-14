`ifndef SYNTHESIS
// SVA bound into the DUT's scope (can see internal nets)
module sky130_fd_sc_hdll__xnor2_sva;

  // Sample on any input/output change
  default clocking cb @ (A or B or Y); endclocking

  // Functional correctness when inputs are known (no X/Z passes)
  a_func_known: assert property (!$isunknown({A,B}) |-> (Y === ~(A ^ B) && !$isunknown(Y)));

  // Buffer must be transparent to internal xnor output
  a_buf_transparent: assert property (Y === xnor0_out_Y);

  // Truth-table coverage (hit all input combinations with correct Y)
  c_tt00: cover property (!A && !B &&  Y);
  c_tt01: cover property (!A &&  B && !Y);
  c_tt10: cover property ( A && !B && !Y);
  c_tt11: cover property ( A &&  B &&  Y);

endmodule

bind sky130_fd_sc_hdll__xnor2 sky130_fd_sc_hdll__xnor2_sva xnor2_sva_i();
`endif
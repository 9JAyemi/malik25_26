// SVA for nand3_gate
`ifndef NAND3_GATE_SVA
`define NAND3_GATE_SVA

module nand3_gate_sva;
  // Bound into nand3_gate; use DUT signals directly

  // Clocking: on any edge of inputs or output
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge Y or negedge Y
  ); endclocking

  // Functional correctness
  a_func_when_known: assert property (!$isunknown({A,B,C}) |-> (Y === ~(A & B & C)));
  a_high_if_any_zero: assert property ((A==1'b0 || B==1'b0 || C==1'b0) |-> (Y==1'b1));
  a_low_only_if_all_ones: assert property ((Y==1'b0) |-> (A==1'b1 && B==1'b1 && C==1'b1));

  // X/Z discipline
  a_no_x_out_when_in_known: assert property (!$isunknown({A,B,C}) |-> !$isunknown(Y));
  a_y_x_requires_in_x:     assert property ($isunknown(Y) |-> $isunknown({A,B,C}));

  // Combinational timing/integrity
  a_zero_delay: assert property ($changed({A,B,C}) |-> ##0 (Y === ~(A & B & C)));
  a_no_spurious_toggle: assert property ($changed(Y) |-> $changed({A,B,C}));

  // Internal wiring sanity (buffers/gate connections)
  a_A_buf_dir: assert property (A_reg === A);
  a_B_buf_dir: assert property (B_reg === B);
  a_C_buf_dir: assert property (C_reg === C);
  a_Y_buf_dir: assert property (Y === Y_and);

  // Power rails (if present)
  a_vdd_one: assert property (VDD === 1'b1);
  a_vss_zero: assert property (VSS === 1'b0);

  // Functional coverage: all input combinations and output value
  c_000: cover property (A==0 && B==0 && C==0 && Y==1);
  c_001: cover property (A==0 && B==0 && C==1 && Y==1);
  c_010: cover property (A==0 && B==1 && C==0 && Y==1);
  c_011: cover property (A==0 && B==1 && C==1 && Y==1);
  c_100: cover property (A==1 && B==0 && C==0 && Y==1);
  c_101: cover property (A==1 && B==0 && C==1 && Y==1);
  c_110: cover property (A==1 && B==1 && C==0 && Y==1);
  c_111: cover property (A==1 && B==1 && C==1 && Y==0);

  // Output toggle coverage
  c_y_rise: cover property ($rose(Y));
  c_y_fall: cover property ($fell(Y));
endmodule

`ifndef SYNTHESIS
bind nand3_gate nand3_gate_sva nand3_gate_sva_i();
`endif

`endif
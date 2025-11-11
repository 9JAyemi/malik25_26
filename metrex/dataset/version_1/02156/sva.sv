// SVA checker for and_module
module and_module_sva(
  input a, input b, input c, input d,
  input out0, input out1, input out2, input out3
);

  // Sample on any change of inputs to this purely combinational DUT
  default clocking cb @(
    posedge a or negedge a or
    posedge b or negedge b or
    posedge c or negedge c or
    posedge d or negedge d
  ); endclocking

  // Functional correctness (4-state accurate)
  ap_out0_func: assert property (out0 === (a & b));
  ap_out1_func: assert property (out1 === (b & c));
  ap_out2_func: assert property (out2 === (a ? d : 1'b0));
  ap_out3_func: assert property (out3 === (b & d));

  // Sanity: if inputs known, outputs must be known
  ap_known: assert property (
    !$isunknown({a,b,c,d}) |-> !$isunknown({out0,out1,out2,out3})
  );

  // One-way implications (helpful debugging invariants)
  ap_out0_imp: assert property (out0 |-> (a && b));
  ap_out1_imp: assert property (out1 |-> (b && c));
  ap_out2_imp: assert property (out2 |-> (a && d));
  ap_out3_imp: assert property (out3 |-> (b && d));
  ap_b_gate:   assert property ((out0 || out1 || out3) |-> b);

  // Quick gating-zero checks
  ap_b_zero: assert property ((b === 1'b0) |-> (!out0 && !out1 && !out3));
  ap_a_zero: assert property ((a === 1'b0) |-> (out2 === 1'b0));

  // Functional coverage (key enable cases and a full-hot case)
  cp_out0_1:  cover property (a && b && out0);
  cp_out1_1:  cover property (b && c && out1);
  cp_out2_1:  cover property (a && d && out2);
  cp_out3_1:  cover property (b && d && out3);
  cp_all_1:   cover property (a && b && c && d &&
                               out0 && out1 && out2 && out3);

  // Toggle coverage for each output
  cp_o0_rise: cover property (!out0 ##1 out0);
  cp_o0_fall: cover property ( out0 ##1 !out0);
  cp_o1_rise: cover property (!out1 ##1 out1);
  cp_o1_fall: cover property ( out1 ##1 !out1);
  cp_o2_rise: cover property (!out2 ##1 out2);
  cp_o2_fall: cover property ( out2 ##1 !out2);
  cp_o3_rise: cover property (!out3 ##1 out3);
  cp_o3_fall: cover property ( out3 ##1 !out3);

endmodule

// Bind the checker to the DUT
bind and_module and_module_sva and_module_sva_i(.*);
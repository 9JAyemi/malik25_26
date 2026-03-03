// SVA checker for and_gate
module and_gate_sva(input logic in1, in2, out);

  // Sample on any edge of inputs or output; use ##0 to allow delta-cycle settle
  default clocking cb @(posedge in1 or negedge in1 or posedge in2 or negedge in2
                        or posedge out or negedge out); endclocking

  // Functional correctness (4-state): out must equal in1 & in2 after delta
  ap_func: assert property (##0 (out === (in1 & in2)))
    else $error("and_gate: out != (in1 & in2)");

  // No spurious output changes without some input change since last sample
  ap_no_spurious: assert property ($changed(out) |-> ($changed(in1) || $changed(in2)))
    else $error("and_gate: out changed without input cause");

  // Functional coverage: all truth-table points observed
  cp_00: cover property (in1==0 && in2==0 && out==0);
  cp_01: cover property (in1==0 && in2==1 && out==0);
  cp_10: cover property (in1==1 && in2==0 && out==0);
  cp_11: cover property (in1==1 && in2==1 && out==1);

  // Output toggle coverage
  cp_out_rise: cover property ($rose(out));
  cp_out_fall: cover property ($fell(out));

endmodule

// Bind into all and_gate instances
bind and_gate and_gate_sva sva_i (.in1(in1), .in2(in2), .out(out));
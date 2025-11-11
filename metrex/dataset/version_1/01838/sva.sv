// SVA bind file for adder_tree_top
// Concise, high-quality checks and coverage

module adder_tree_top_sva;
  localparam int AW = `ADDER_WIDTH;

  default clocking cb @(posedge clk); endclocking

  // Basic knownness on output
  assert property (!$isunknown(sum));

  // Leaf registers capture inputs (1-cycle latency)
  assert property (sum0_0_0_0 == $past(isum0_0_0_0));
  assert property (sum0_0_0_1 == $past(isum0_0_0_1));
  assert property (sum0_0_1_0 == $past(isum0_0_1_0));
  assert property (sum0_0_1_1 == $past(isum0_0_1_1));
  assert property (sum0_1_0_0 == $past(isum0_1_0_0));
  assert property (sum0_1_0_1 == $past(isum0_1_0_1));
  assert property (sum0_1_1_0 == $past(isum0_1_1_0));
  assert property (sum0_1_1_1 == $past(isum0_1_1_1));

  // Combinational adders correct at each level
  assert property (sum0_0_0 == (sum0_0_0_0 + sum0_0_0_1));
  assert property (sum0_0_1 == (sum0_0_1_0 + sum0_0_1_1));
  assert property (sum0_1_0 == (sum0_1_0_0 + sum0_1_0_1));
  assert property (sum0_1_1 == (sum0_1_1_0 + sum0_1_1_1));
  assert property (sum0_0 == (sum0_0_0 + sum0_0_1));
  assert property (sum0_1 == (sum0_1_0 + sum0_1_1));
  assert property (sum0   == (sum0_0   + sum0_1  ));

`ifdef 3_LEVEL_ADDER
  // Pipeline alignment and full 8-input arithmetic equivalence (with truncation check)
  assert property ( sum == $past(sum0[AW:0]) );
  assert property ( sum == $past( ({3'b0,isum0_0_0_0}+{3'b0,isum0_0_0_1}+{3'b0,isum0_0_1_0}+{3'b0,isum0_0_1_1}
                                 +{3'b0,isum0_1_0_0}+{3'b0,isum0_1_0_1}+{3'b0,isum0_1_1_0}+{3'b0,isum0_1_1_1})[AW:0] ) );
  // Detect loss of precision: top 2 bits of sum0 must be zero (sum output is only AW+1 bits)
  assert property ( sum0[AW+2:AW+1] == '0 );

  // Minimal but meaningful coverage
  cover property ($changed(sum));
  cover property (sum0_0_0[AW]); // carry out at L3 (one subtree)
  cover property (sum0_0_1[AW]);
  cover property (sum0_1_0[AW]);
  cover property (sum0_1_1[AW]);
`endif

`ifdef 2_LEVEL_ADDER
  // Pipeline alignment and 4-input arithmetic equivalence (with truncation check)
  assert property ( sum == $past(sum0_0[AW:0]) );
  assert property ( sum == $past( ({2'b0,isum0_0_0_0}+{2'b0,isum0_0_0_1}+{2'b0,isum0_0_1_0}+{2'b0,isum0_0_1_1})[AW:0] ) );
  // Detect loss of precision: top bit of sum0_0 must be zero (sum output is only AW+1 bits)
  assert property ( sum0_0[AW+1] == 1'b0 );

  // Minimal but meaningful coverage
  cover property ($changed(sum));
  cover property (sum0_0_0[AW]); // carry out at L3
  cover property (sum0_0_1[AW]);
`endif
endmodule

bind adder_tree_top adder_tree_top_sva sva_i();
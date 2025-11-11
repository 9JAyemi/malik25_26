// SVA for adder_tree_top
// Bind into the DUT; no DUT edits required.
bind adder_tree_top adder_tree_top_sva();

module adder_tree_top_sva;

  // Default clocking
  default clocking cb @(posedge clk); endclocking

  // Track availability of $past()
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Local widths
  localparam int W  = $bits(sum);
  localparam int W3 = $bits(sum0);
  localparam int W2 = $bits(sum0_0);
  localparam int W1 = $bits(sum0_0_0);

  // -------------------------
  // Structural/static checks
  // -------------------------
  initial begin
    // Width grows by +1 each adder level
    assert ($bits(sum0_0_0) == $bits(isum0_0_0_0)+1) else $error("L3 width mismatch");
    assert ($bits(sum0_0)   == $bits(sum0_0_0)+1)    else $error("L2 width mismatch");
    assert ($bits(sum0)     == $bits(sum0_0)+1)      else $error("L1 width mismatch");
  end

  // -------------------------
  // Register capture checks
  // -------------------------
  assert property (past_valid |-> sum0_0_0_0 == $past(isum0_0_0_0));
  assert property (past_valid |-> sum0_0_0_1 == $past(isum0_0_0_1));
  assert property (past_valid |-> sum0_0_1_0 == $past(isum0_0_1_0));
  assert property (past_valid |-> sum0_0_1_1 == $past(isum0_0_1_1));
  assert property (past_valid |-> sum0_1_0_0 == $past(isum0_1_0_0));
  assert property (past_valid |-> sum0_1_0_1 == $past(isum0_1_0_1));
  assert property (past_valid |-> sum0_1_1_0 == $past(isum0_1_1_0));
  assert property (past_valid |-> sum0_1_1_1 == $past(isum0_1_1_1));

  // -------------------------
  // Combinational adder checks (per level)
  // Guard against X on operands to avoid vacuous results.
  // -------------------------
  assert property (
    !$isunknown({sum0_0_0_0,sum0_0_0_1,sum0_0_0}) |-> sum0_0_0 == sum0_0_0_0 + sum0_0_0_1
  );
  assert property (
    !$isunknown({sum0_0_1_0,sum0_0_1_1,sum0_0_1}) |-> sum0_0_1 == sum0_0_1_0 + sum0_0_1_1
  );
  assert property (
    !$isunknown({sum0_1_0_0,sum0_1_0_1,sum0_1_0}) |-> sum0_1_0 == sum0_1_0_0 + sum0_1_0_1
  );
  assert property (
    !$isunknown({sum0_1_1_0,sum0_1_1_1,sum0_1_1}) |-> sum0_1_1 == sum0_1_1_0 + sum0_1_1_1
  );
  assert property (
    !$isunknown({sum0_0,sum0_1,sum0}) |-> sum0 == sum0_0 + sum0_1
  );
  assert property (
    !$isunknown({sum0_0_0,sum0_0_1,sum0_0}) |-> sum0_0 == sum0_0_0 + sum0_0_1
  );
  assert property (
    !$isunknown({sum0_1_0,sum0_1_1,sum0_1}) |-> sum0_1 == sum0_1_0 + sum0_1_1
  );

  // -------------------------
  // Pipeline/latency and width-truncation checks
  // -------------------------
`ifdef 3_LEVEL_ADDER
  // Sum updates one cycle later to the L1 result
  assert property (past_valid |-> ##1 sum == $past(sum0));

  // No truncation: top growth bits of sum0 must be zero before assignment to sum
  assert property (sum0[W3-1:W] == '0);

  // End-to-end arithmetic from inputs (one-cycle latency), guarded against X
  assert property (
    past_valid && !$isunknown({isum0_0_0_0,isum0_0_0_1,isum0_0_1_0,isum0_0_1_1,
                               isum0_1_0_0,isum0_1_0_1,isum0_1_1_0,isum0_1_1_1})
    |-> ##1 sum == $past( {{(W-$bits(isum0_0_0_0)){1'b0}}, isum0_0_0_0}
                        + {{(W-$bits(isum0_0_0_1)){1'b0}}, isum0_0_0_1}
                        + {{(W-$bits(isum0_0_1_0)){1'b0}}, isum0_0_1_0}
                        + {{(W-$bits(isum0_0_1_1)){1'b0}}, isum0_0_1_1}
                        + {{(W-$bits(isum0_1_0_0)){1'b0}}, isum0_1_0_0}
                        + {{(W-$bits(isum0_1_0_1)){1'b0}}, isum0_1_0_1}
                        + {{(W-$bits(isum0_1_1_0)){1'b0}}, isum0_1_1_0}
                        + {{(W-$bits(isum0_1_1_1)){1'b0}}, isum0_1_1_1} )
  );
`elsif 2_LEVEL_ADDER
  // Sum updates one cycle later to the L2_0 result (as coded)
  assert property (past_valid |-> ##1 sum == $past(sum0_0));

  // No truncation: top growth bit of sum0_0 must be zero before assignment to sum
  assert property (sum0_0[W2-1:W] == '0);

  // Even in 2-level mode, the mathematically correct total should be sum of all 8 inputs.
  // This assertion will flag any unintended omission.
  assert property (
    past_valid && !$isunknown({isum0_0_0_0,isum0_0_0_1,isum0_0_1_0,isum0_0_1_1,
                               isum0_1_0_0,isum0_1_0_1,isum0_1_1_0,isum0_1_1_1})
    |-> ##1 sum == $past( {{(W-$bits(isum0_0_0_0)){1'b0}}, isum0_0_0_0}
                        + {{(W-$bits(isum0_0_0_1)){1'b0}}, isum0_0_0_1}
                        + {{(W-$bits(isum0_0_1_0)){1'b0}}, isum0_0_1_0}
                        + {{(W-$bits(isum0_0_1_1)){1'b0}}, isum0_0_1_1}
                        + {{(W-$bits(isum0_1_0_0)){1'b0}}, isum0_1_0_0}
                        + {{(W-$bits(isum0_1_0_1)){1'b0}}, isum0_1_0_1}
                        + {{(W-$bits(isum0_1_1_0)){1'b0}}, isum0_1_1_0}
                        + {{(W-$bits(isum0_1_1_1)){1'b0}}, isum0_1_1_1} )
  );
`else
  initial $warning("No 3_LEVEL_ADDER/2_LEVEL_ADDER defined; SVA expectations limited.");
`endif

  // Output X-propagation: known inputs imply known sum one cycle later
  assert property (
    past_valid && !$isunknown({isum0_0_0_0,isum0_0_0_1,isum0_0_1_0,isum0_0_1_1,
                               isum0_1_0_0,isum0_1_0_1,isum0_1_1_0,isum0_1_1_1})
    |-> ##1 !$isunknown(sum)
  );

  // -------------------------
  // Targeted functional coverage
  // -------------------------
  // Extremes
  cover property (past_valid ##1 (sum == '0));
  cover property (past_valid ##1 (sum == {W{1'b1}}));

  // Exercise MSBs in each level
  cover property (sum0_0_0[W1-1]);
  cover property (sum0_0_1[W1-1]);
  cover property (sum0_1_0[W1-1]);
  cover property (sum0_1_1[W1-1]);

`ifdef 3_LEVEL_ADDER
  // Hit top bit of final sum without overflow
  cover property (sum0[W3-1:W] == '0 && sum0[W-1]);
`elsif 2_LEVEL_ADDER
  cover property (sum0_0[W2-1:W] == '0 && sum0_0[W-1]);
`endif

endmodule
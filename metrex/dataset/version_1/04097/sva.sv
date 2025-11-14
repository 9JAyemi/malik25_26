// SVA for adder_tree_top and adder_tree_branch
// Bind-in; no DUT edits required.

bind adder_tree_top adder_tree_top_sva();
module adder_tree_top_sva;
  localparam int W = `ADDER_WIDTH;

  // Startup gating for $past()
  bit started;
  initial started = 1'b0;
  always @(posedge clk) started <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!started)

  // Static width sanity checks (compile-time)
  initial begin
    assert ($bits(sum)        == W+1) else $error("sum width != ADDER_WIDTH+1");
    assert ($bits(sum0)       == W+3);
    assert ($bits(sum0_0)     == W+2);
    assert ($bits(sum0_1)     == W+2);
    assert ($bits(sum0_0_0)   == W+1);
    assert ($bits(sum0_0_1)   == W+1);
    assert ($bits(sum0_1_0)   == W+1);
    assert ($bits(sum0_1_1)   == W+1);
    assert ($bits(sum0_0_0_0) == W);
    assert ($bits(sum0_0_0_1) == W);
    assert ($bits(sum0_0_1_0) == W);
    assert ($bits(sum0_0_1_1) == W);
    assert ($bits(sum0_1_0_0) == W);
    assert ($bits(sum0_1_0_1) == W);
    assert ($bits(sum0_1_1_0) == W);
    assert ($bits(sum0_1_1_1) == W);
  end

  // No X/Z on key signals after first cycle
  assert property (!$isunknown({isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1,
                                isum0_1_0_0, isum0_1_0_1, isum0_1_1_0, isum0_1_1_1, sum})));

  // Pipeline register correctness (1-cycle)
  assert property (sum0_0_0_0 == $past(isum0_0_0_0));
  assert property (sum0_0_0_1 == $past(isum0_0_0_1));
  assert property (sum0_0_1_0 == $past(isum0_0_1_0));
  assert property (sum0_0_1_1 == $past(isum0_0_1_1));
  assert property (sum0_1_0_0 == $past(isum0_1_0_0));
  assert property (sum0_1_0_1 == $past(isum0_1_0_1));
  assert property (sum0_1_1_0 == $past(isum0_1_1_0));
  assert property (sum0_1_1_1 == $past(isum0_1_1_1));

  // Combinational adder-tree correctness (within cycle)
  // L3
  assert property (sum0_0_0 == sum0_0_0_0 + sum0_0_0_1);
  assert property (sum0_0_1 == sum0_0_1_0 + sum0_0_1_1);
  assert property (sum0_1_0 == sum0_1_0_0 + sum0_1_0_1);
  assert property (sum0_1_1 == sum0_1_1_0 + sum0_1_1_1);
  // L2
  assert property (sum0_0   == sum0_0_0   + sum0_0_1);
  assert property (sum0_1   == sum0_1_0   + sum0_1_1);
  // L1
  assert property (sum0     == sum0_0     + sum0_1);

  // Output register matches selected level, truncated to sum width
`ifdef 2_LEVEL_ADDER
  assert property (sum == $past(sum0_0[W:0]));
  // End-to-end: equals sum of four inputs from previous cycle (lower W+1 bits)
  assert property (sum == ((($past(isum0_0_0_0)+$past(isum0_0_0_1))
                          + ($past(isum0_0_1_0)+$past(isum0_0_1_1))))[W:0]));
`endif
`ifdef 3_LEVEL_ADDER
  assert property (sum == $past(sum0[W:0]));
  // End-to-end: equals sum of all eight inputs from previous cycle (lower W+1 bits)
  assert property (sum == ((($past(isum0_0_0_0)+$past(isum0_0_0_1))
                          + ($past(isum0_0_1_0)+$past(isum0_0_1_1))
                          + ($past(isum0_1_0_0)+$past(isum0_1_0_1))
                          + ($past(isum0_1_1_0)+$past(isum0_1_1_1)))[W:0]));
`endif

  // Minimal functional coverage
  cover property (sum0_0_0[W]);  // carry at L3_0
  cover property (sum0_0_1[W]);  // carry at L3_1
  cover property (sum0_1_0[W]);  // carry at L3_2
  cover property (sum0_1_1[W]);  // carry at L3_3
  cover property (sum[W]);       // MSB of output set
`ifdef 3_LEVEL_ADDER
  cover property (sum0_0 != '0 && sum0_1 != '0); // both halves active
`endif
`ifdef 2_LEVEL_ADDER
  cover property (sum0_0 != '0);                 // active half in 2-level mode
`endif
endmodule


bind adder_tree_branch adder_tree_branch_sva();
module adder_tree_branch_sva;
  localparam int WB = `ADDER_WIDTH + EXTRA_BITS;
  // Static width check
  initial begin
    assert ($bits(a)   == WB);
    assert ($bits(b)   == WB);
    assert ($bits(sum) == WB+1);
  end
  // Combinational correctness
  always @* assert (sum == a + b);
  // Simple coverage: see a carry-out at least once
  always @* cover (sum[WB] && (a!='0) && (b!='0));
endmodule
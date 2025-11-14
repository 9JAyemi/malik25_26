// SVA for adder_tree_top and adder_tree_branch
// Concise, high-quality checks with end-to-end functional assertions, latency, overflow detection, and basic coverage.

`ifndef SVA_ADDERTREE_SVA
`define SVA_ADDERTREE_SVA

// Checker for each combinational adder_tree_branch
module adder_tree_branch_sva;
  // Immediate assertions (combinational block)
  always_comb begin
    // No X/Z on ports
    assert (!$isunknown({a,b,sum})) else $error("adder_tree_branch: X/Z on {a,b,sum}");
    // Functional correctness
    assert (sum == a + b) else $error("adder_tree_branch: sum != a+b");
  end
endmodule

bind adder_tree_branch adder_tree_branch_sva branch_chk();

// Top-level checker bound inside adder_tree_top scope (sees internal signals)
module adder_tree_top_sva;

  // Compile-time width sanity (catches accidental edits)
  initial begin
    assert ($bits(sum)    == `ADDER_WIDTH+1) else $error("sum width mismatch");
    assert ($bits(sum0_0) == `ADDER_WIDTH+2) else $error("sum0_0 width mismatch");
    assert ($bits(sum0_1) == `ADDER_WIDTH+2) else $error("sum0_1 width mismatch");
    assert ($bits(sum0)   == `ADDER_WIDTH+3) else $error("sum0 width mismatch");
  end

  // Clocking and past gating
  bit past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default clocking cb @(posedge clk); endclocking

  // Inputs/outputs must be known each cycle
  assert property (cb !$isunknown({
      isum0_0_0_0,isum0_0_0_1,isum0_0_1_0,isum0_0_1_1,
      isum0_1_0_0,isum0_1_0_1,isum0_1_1_0,isum0_1_1_1, sum
  })) else $error("adder_tree_top: X/Z on inputs or sum");

  // Register capture latency: input regs equal prior-cycle inputs
  assert property (cb disable iff(!past_valid)
    {sum0_0_0_0,sum0_0_0_1,sum0_0_1_0,sum0_0_1_1,
     sum0_1_0_0,sum0_1_0_1,sum0_1_1_0,sum0_1_1_1}
    == $past({
     isum0_0_0_0,isum0_0_0_1,isum0_0_1_0,isum0_0_1_1,
     isum0_1_0_0,isum0_1_0_1,isum0_1_1_0,isum0_1_1_1
    })
  ) else $error("adder_tree_top: input register capture mismatch");

  // Output is registered; no mid-cycle glitches
  assert property (@(negedge clk) $stable(sum))
    else $error("adder_tree_top: sum changed outside posedge");

  // End-to-end functionality and overflow/truncation checks (1-cycle latency)
`ifdef 2_LEVEL_ADDER
  // Expected: sum of first 4 inputs only (isum0_0_*_*), 1-cycle latency
  assert property (cb disable iff(!past_valid)
    sum == ($past(isum0_0_0_0) + $past(isum0_0_0_1)
          + $past(isum0_0_1_0) + $past(isum0_0_1_1))[`ADDER_WIDTH:0]
  ) else $error("adder_tree_top: 2-level end-to-end mismatch");

  // Detect lost carry due to width truncation (sum has ADDER_WIDTH+1 bits)
  assert property (cb disable iff(!past_valid)
    (($past(isum0_0_0_0) + $past(isum0_0_0_1)
     +$past(isum0_0_1_0) + $past(isum0_0_1_1))
      [`ADDER_WIDTH+1:`ADDER_WIDTH+1] == '0)
  ) else $error("adder_tree_top: 2-level overflow (MSB truncated)");
`elsif defined(3_LEVEL_ADDER)
  // Expected: sum of all 8 inputs, 1-cycle latency
  assert property (cb disable iff(!past_valid)
    sum == ($past(isum0_0_0_0) + $past(isum0_0_0_1)
          + $past(isum0_0_1_0) + $past(isum0_0_1_1)
          + $past(isum0_1_0_0) + $past(isum0_1_0_1)
          + $past(isum0_1_1_0) + $past(isum0_1_1_1))[`ADDER_WIDTH:0]
  ) else $error("adder_tree_top: 3-level end-to-end mismatch");

  // Detect lost carries due to width truncation (two MSBs would be dropped)
  assert property (cb disable iff(!past_valid)
    (($past(isum0_0_0_0) + $past(isum0_0_0_1)
     +$past(isum0_0_1_0) + $past(isum0_0_1_1)
     +$past(isum0_1_0_0) + $past(isum0_1_0_1)
     +$past(isum0_1_1_0) + $past(isum0_1_1_1))
      [`ADDER_WIDTH+2:`ADDER_WIDTH+1] == '0)
  ) else $error("adder_tree_top: 3-level overflow (MSBs truncated)");
`else
  initial $error("Neither 2_LEVEL_ADDER nor 3_LEVEL_ADDER defined");
`endif

  // Lightweight coverage: exercise carries at each adder level
  // L3 carries (pairwise adds)
  cover property (cb disable iff(!past_valid) $past(sum0_0_0[`ADDER_WIDTH])); // isum0_0_* pair 0
  cover property (cb disable iff(!past_valid) $past(sum0_0_1[`ADDER_WIDTH])); // isum0_0_* pair 1
  cover property (cb disable iff(!past_valid) $past(sum0_1_0[`ADDER_WIDTH])); // isum0_1_* pair 0
  cover property (cb disable iff(!past_valid) $past(sum0_1_1[`ADDER_WIDTH])); // isum0_1_* pair 1
  // L2 carries (sum of two 23-bit results)
  cover property (cb disable iff(!past_valid) $past(sum0_0[`ADDER_WIDTH+1]));
  cover property (cb disable iff(!past_valid) $past(sum0_1[`ADDER_WIDTH+1]));
`ifdef 3_LEVEL_ADDER
  // L1 carry (final 25-bit sum)
  cover property (cb disable iff(!past_valid) $past(sum0[`ADDER_WIDTH+2]));
`endif

endmodule

bind adder_tree_top adder_tree_top_sva top_chk();

`endif // SVA_ADDERTREE_SVA
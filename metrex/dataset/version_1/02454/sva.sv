// SVA for adder_tree_top and adder_tree_branch
// Bind into DUT scopes; concise checks with strong functional and structural coverage

// Checker for the leaf adder branches
module adder_tree_branch_sva;
  localparam int WA = $bits(a);
  localparam int WB = $bits(b);
  localparam int WS = $bits(sum);
  initial begin
    assert (WA == WB) else $error("adder_tree_branch: a/b width mismatch");
    assert (WS == WA+1) else $error("adder_tree_branch: sum width must be a+1");
  end
  always_comb assert (#0 sum == a + b)
    else $error("adder_tree_branch: sum != a+b");
endmodule

// Checker for the top-level adder tree
module adder_tree_top_sva;
  // Width sanity
  localparam int WIN = $bits(isum0_0_0_0);
  localparam int WL3 = $bits(sum0_0_0);
  localparam int WL2 = $bits(sum0_0);
  localparam int WL1 = $bits(sum0);
  localparam int WS  = $bits(sum);
  localparam int PAD = (WS>WIN)?(WS-WIN):0;

  function automatic [WS-1:0] zext(input logic [WIN-1:0] x);
    if (WS>=WIN) zext = {{PAD{1'b0}}, x};
    else zext = x[WS-1:0];
  endfunction

  initial begin
    assert (WL3 == WIN+1) else $error("L3 width must be WIN+1");
    assert (WL2 == WL3+1) else $error("L2 width must be L3+1");
    assert (WL1 == WL2+1) else $error("L1 width must be L2+1");
`ifdef 3_LEVEL_ADDER
    assert (WS == WL1) else $error("sum width must match sum0 (3-level)");
`elsif 2_LEVEL_ADDER
    assert (WS == WL2) else $error("sum width must match sum0_0 (2-level)");
`endif
  end

  // Structural invariant at L1
  assert property (@(posedge clk) sum0 == sum0_0 + sum0_1)
    else $error("sum0 != sum0_0 + sum0_1");

`ifdef 3_LEVEL_ADDER
  // Pipeline relation to intermediate sum
  assert property (@(posedge clk) disable iff ($initstate) sum == $past(sum0))
    else $error("sum != $past(sum0)");
`elsif 2_LEVEL_ADDER
  assert property (@(posedge clk) disable iff ($initstate) sum == $past(sum0_0))
    else $error("sum != $past(sum0_0)");
`endif

  // End-to-end functional check: 1-cycle delayed 8-input sum
  assert property (@(posedge clk) disable iff ($initstate)
    sum == ( zext($past(isum0_0_0_0)) + zext($past(isum0_0_0_1)) +
             zext($past(isum0_0_1_0)) + zext($past(isum0_0_1_1)) +
             zext($past(isum0_1_0_0)) + zext($past(isum0_1_0_1)) +
             zext($past(isum0_1_1_0)) + zext($past(isum0_1_1_1)) )
  ) else $error("sum != 1-cycle delayed sum of 8 inputs");

  // Leaf register capture (1-cycle)
  assert property (@(posedge clk) disable iff ($initstate)
    {sum0_0_0_0, sum0_0_0_1, sum0_0_1_0, sum0_0_1_1,
     sum0_1_0_0, sum0_1_0_1, sum0_1_1_0, sum0_1_1_1}
    == $past({isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1,
              isum0_1_0_0, isum0_1_0_1, isum0_1_1_0, isum0_1_1_1})
  ) else $error("Leaf regs != $past(inputs)");

  // Guard against truncation if output is undersized
`ifdef 3_LEVEL_ADDER
  if (WL1 > WS) begin
    assert property (@(posedge clk) disable iff ($initstate) sum0[WL1-1:WS] == '0)
      else $error("Truncation: sum loses significant bits of sum0");
  end
`elsif 2_LEVEL_ADDER
  if (WL2 > WS) begin
    assert property (@(posedge clk) disable iff ($initstate) sum0_0[WL2-1:WS] == '0)
      else $error("Truncation: sum loses significant bits of sum0_0");
  end
`endif

  // Known-in => known-out next cycle
  assert property (@(posedge clk) disable iff ($initstate)
    !$isunknown($past({isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1,
                       isum0_1_0_0, isum0_1_0_1, isum0_1_1_0, isum0_1_1_1}))
    |-> !$isunknown(sum)
  ) else $error("X/Z observed on sum with known inputs");

  // Coverage
  cover property (@(posedge clk) disable iff ($initstate) sum == '0);
  cover property (@(posedge clk) sum0[WL1-1]);
  cover property (@(posedge clk) sum0_0[WL2-1]);
  cover property (@(posedge clk)
    (sum0_0_0[WL3-1] || sum0_0_1[WL3-1] || sum0_1_0[WL3-1] || sum0_1_1[WL3-1])
  );
  cover property (@(posedge clk) disable iff ($initstate)
    $past({isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1,
           isum0_1_0_0, isum0_1_0_1, isum0_1_1_0, isum0_1_1_1})
    == {8{{WIN{1'b1}}}} and sum0[WL1-1]
  );
endmodule

bind adder_tree_branch adder_tree_branch_sva sva_branch();
bind adder_tree_top    adder_tree_top_sva    sva_top();
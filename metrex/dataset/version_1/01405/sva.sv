// SVA binders for adder_tree_top and adder_tree_branch
// Concise, focuses on functional correctness, structure, X-checks, and key coverage.

module adder_tree_top_sva #(parameter int W = `ADDER_WIDTH)
(
  input clk,
  // DUT I/Os
  input [W-1:0]  isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1,
                 isum0_1_0_0, isum0_1_0_1, isum0_1_1_0, isum0_1_1_1,
  input [W:0]    sum,
  // Internal nets (structure checks)
  input [W+2:0]  sum0,
  input [W+1:0]  sum0_0, sum0_1,
  input [W:0]    sum0_0_0, sum0_0_1, sum0_1_0, sum0_1_1,
  input [W-1:0]  sum0_0_0_0, sum0_0_0_1, sum0_0_1_0, sum0_0_1_1,
                 sum0_1_0_0, sum0_1_0_1, sum0_1_1_0, sum0_1_1_1
);

  // Helper: zero-extend a W-bit operand to W+2 bits (safe for sum of 4 terms)
  function automatic logic [W+1:0] ext2(input logic [W-1:0] x);
    ext2 = {2'b0, x};
  endfunction

  // Expected sums (computed wide, then sliced as needed)
  wire [W+1:0] s00 = ext2(isum0_0_0_0) + ext2(isum0_0_0_1);
  wire [W+1:0] s01 = ext2(isum0_0_1_0) + ext2(isum0_0_1_1);
  wire [W+1:0] s10 = ext2(isum0_1_0_0) + ext2(isum0_1_0_1);
  wire [W+1:0] s11 = ext2(isum0_1_1_0) + ext2(isum0_1_1_1);

  wire [W+1:0] sum4_left  = s00 + s01; // 4-term sum (left subtree)
  wire [W+1:0] sum4_right = s10 + s11; // 4-term sum (right subtree)
  wire [W+2:0] sum8_full  = {1'b0, sum4_left} + {1'b0, sum4_right}; // 8-term sum

  default clocking cb @(posedge clk); endclocking

  // Structural correctness of adder tree (combinational branches)
  assert property (sum0_0_0 == {1'b0,sum0_0_0_0} + {1'b0,sum0_0_0_1});
  assert property (sum0_0_1 == {1'b0,sum0_0_1_0} + {1'b0,sum0_0_1_1});
  assert property (sum0_1_0 == {1'b0,sum0_1_0_0} + {1'b0,sum0_1_0_1});
  assert property (sum0_1_1 == {1'b0,sum0_1_1_0} + {1'b0,sum0_1_1_1});
  assert property (sum0_0   == {1'b0,sum0_0_0}   + {1'b0,sum0_0_1});
  assert property (sum0_1   == {1'b0,sum0_1_0}   + {1'b0,sum0_1_1});
  assert property (sum0     == {1'b0,sum0_0}     + {1'b0,sum0_1});

  // Functional correctness of final output (1-cycle latency, truncated to W+1 bits)
  `ifdef 2_LEVEL_ADDER
    assert property (sum == $past(sum4_left[W:0]));
  `elsif 3_LEVEL_ADDER
    assert property (sum == $past(sum8_full[W:0]));
  `else
    // Default to 2-level behavior if no macro selected
    assert property (sum == $past(sum4_left[W:0]));
  `endif

  // X/Z checks on critical signals
  assert property (!$isunknown({
    sum,
    sum0, sum0_0, sum0_1, sum0_0_0, sum0_0_1, sum0_1_0, sum0_1_1,
    sum0_0_0_0, sum0_0_0_1, sum0_0_1_0, sum0_0_1_1, sum0_1_0_0, sum0_1_0_1, sum0_1_1_0, sum0_1_1_1,
    isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1, isum0_1_0_0, isum0_1_0_1, isum0_1_1_0, isum0_1_1_1
  }));

  // Key coverage
  cover property ($changed(sum));
  `ifdef 2_LEVEL_ADDER
    cover property (sum4_left[W+1]); // overflow bit (dropped by sum) seen
  `elsif 3_LEVEL_ADDER
    cover property (sum8_full[W+2]); // overflow bit (dropped by sum) seen
    cover property ((sum4_left != '0) && (sum4_right != '0)); // both subtrees active
  `endif

endmodule

module adder_tree_branch_sva #(parameter int EXTRA_BITS = 0, parameter int W = `ADDER_WIDTH)
(
  input [W+EXTRA_BITS-1:0] a,
  input [W+EXTRA_BITS-1:0] b,
  input [W+EXTRA_BITS:0]   sum
);
  // Combinational correctness of branch
  always_comb assert (sum == a + b);
endmodule

// Bind SVA to DUTs
bind adder_tree_top     adder_tree_top_sva     #(.W(`ADDER_WIDTH)) u_adder_tree_top_sva (.*);
bind adder_tree_branch  adder_tree_branch_sva  #(.EXTRA_BITS(EXTRA_BITS), .W(`ADDER_WIDTH)) u_adder_tree_branch_sva (.*);
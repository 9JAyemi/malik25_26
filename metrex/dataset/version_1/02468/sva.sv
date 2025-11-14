// SVA for adder_tree_top and adder_tree_branch
// Focus: functional correctness, latency, structural arithmetic, X-propagation, concise coverage.

`ifndef ADDER_TREE_SVA
`define ADDER_TREE_SVA

// Bind to each branch: sum must equal a+b at all times (combinational)
module adder_tree_branch_sva
  #(parameter int W = `ADDER_WIDTH,
    parameter int EXTRA_BITS = 0)
  (input logic [W+EXTRA_BITS-1:0] a,
   input logic [W+EXTRA_BITS-1:0] b,
   input logic [W+EXTRA_BITS  :0] sum);

  // Immediate check for combinational correctness and Xs
  always_comb begin
    assert (!$isunknown({a,b,sum})) else $error("adder_tree_branch has X/Z on ports");
    assert (sum == a + b) else $error("adder_tree_branch sum != a+b");
  end
endmodule

bind adder_tree_branch adder_tree_branch_sva
  #(.W(`ADDER_WIDTH), .EXTRA_BITS(EXTRA_BITS))
  u_adder_tree_branch_sva (.a(a), .b(b), .sum(sum));


// Top-level SVA: latency, tree composition, overflow coverage, X checks
module adder_tree_top_sva
  #(parameter int W = `ADDER_WIDTH)
  (input  logic                 clk,
   // inputs
   input  logic [W-1:0]         isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1,
                                isum0_1_0_0, isum0_1_0_1, isum0_1_1_0, isum0_1_1_1,
   // output
   input  logic [W:0]           sum,
   // internal tree wires
   input  logic [W+3-1:0]       sum0,
   input  logic [W+2-1:0]       sum0_0, sum0_1,
   input  logic [W+1-1:0]       sum0_0_0, sum0_0_1, sum0_1_0, sum0_1_1,
   // registered leaf terms
   input  logic [W-1:0]         reg_sum0_0_0_0, reg_sum0_0_0_1, reg_sum0_0_1_0, reg_sum0_0_1_1,
                                reg_sum0_1_0_0, reg_sum0_1_0_1, reg_sum0_1_1_0, reg_sum0_1_1_1);

  // Helper: full 8-input sum (W+3 bits)
  function automatic logic [W+3-1:0] add8
    (input logic [W-1:0] a0,a1,a2,a3,a4,a5,a6,a7);
    logic [W  :0] s0 = a0 + a1;
    logic [W  :0] s1 = a2 + a3;
    logic [W  :0] s2 = a4 + a5;
    logic [W  :0] s3 = a6 + a7;
    logic [W+1:0] s01 = s0 + s1;
    logic [W+1:0] s23 = s2 + s3;
    add8 = s01 + s23; // W+2 + 1 = W+3 bits
  endfunction

  // Known-value checks on IO
  property p_no_x_inputs; @(posedge clk) !$isunknown({
      isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1,
      isum0_1_0_0, isum0_1_0_1, isum0_1_1_0, isum0_1_1_1, sum
  }); endproperty
  assert property (p_no_x_inputs) else $error("adder_tree_top has X/Z on IO");

  // Leaf registers capture 1-cycle latency from inputs
  // (disable on first cycle to avoid $past unknown)
  `define ASSERT_REG_CAP(r,i) \
    assert property (@(posedge clk) disable iff ($initstate) (r == $past(i))) \
      else $error("Leaf register mismatch: %s != past(%s)", `"r`", `"i`")

  `ASSERT_REG_CAP(reg_sum0_0_0_0, isum0_0_0_0);
  `ASSERT_REG_CAP(reg_sum0_0_0_1, isum0_0_0_1);
  `ASSERT_REG_CAP(reg_sum0_0_1_0, isum0_0_1_0);
  `ASSERT_REG_CAP(reg_sum0_0_1_1, isum0_0_1_1);
  `ASSERT_REG_CAP(reg_sum0_1_0_0, isum0_1_0_0);
  `ASSERT_REG_CAP(reg_sum0_1_0_1, isum0_1_0_1);
  `ASSERT_REG_CAP(reg_sum0_1_1_0, isum0_1_1_0);
  `ASSERT_REG_CAP(reg_sum0_1_1_1, isum0_1_1_1);
  `undef ASSERT_REG_CAP

  // Check each adder-tree level composition at the top scope
  assert property (@(posedge clk) (sum0_0_0 == reg_sum0_0_0_0 + reg_sum0_0_0_1))
    else $error("L3_0 mismatch");
  assert property (@(posedge clk) (sum0_0_1 == reg_sum0_0_1_0 + reg_sum0_0_1_1))
    else $error("L3_1 mismatch");
  assert property (@(posedge clk) (sum0_1_0 == reg_sum0_1_0_0 + reg_sum0_1_0_1))
    else $error("L3_2 mismatch");
  assert property (@(posedge clk) (sum0_1_1 == reg_sum0_1_1_0 + reg_sum0_1_1_1))
    else $error("L3_3 mismatch");

  assert property (@(posedge clk) (sum0_0 == sum0_0_0 + sum0_0_1))
    else $error("L2_0 mismatch");
  assert property (@(posedge clk) (sum0_1 == sum0_1_0 + sum0_1_1))
    else $error("L2_1 mismatch");

  assert property (@(posedge clk) (sum0 == sum0_0 + sum0_1))
    else $error("L1_0 mismatch");

  // Top result must equal 8-input sum (modulo W+1 bits) with 1-cycle latency
  assert property (@(posedge clk) disable iff ($initstate)
    sum == $past(add8(isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1,
                      isum0_1_0_0, isum0_1_0_1, isum0_1_1_0, isum0_1_1_1)[W:0]))
    else $error("Top sum mismatch vs 8-input addition (modulo %0d bits)", W+1);

  // Also check consistency with internal low bits used to drive sum
  `ifdef 3_LEVEL_ADDER
    assert property (@(posedge clk) disable iff ($initstate)
      sum == $past(sum0[W:0])) else $error("sum != past(sum0[W:0])");
    // Coverage: observe internal overflow beyond output width
    cover property (@(posedge clk) disable iff ($initstate) (sum0[W+2:W+1] != '0));
  `elsif 2_LEVEL_ADDER
    assert property (@(posedge clk) disable iff ($initstate)
      sum == $past(sum0_0[W:0])) else $error("sum != past(sum0_0[W:0])");
    // Coverage: observe internal overflow beyond output width
    cover property (@(posedge clk) disable iff ($initstate) (sum0_0[W+1] != 1'b0));
  `else
    // If neither mode is selected, sum is not driven here; flag it.
    initial $warning("Neither 3_LEVEL_ADDER nor 2_LEVEL_ADDER defined; sum may be stale.");
  `endif

  // Coverage: MSB of output toggles high at least once
  cover property (@(posedge clk) disable iff ($initstate) sum[W] == 1'b1);

endmodule

bind adder_tree_top adder_tree_top_sva #(.W(`ADDER_WIDTH)) u_adder_tree_top_sva (
  .clk(clk),
  .isum0_0_0_0(isum0_0_0_0), .isum0_0_0_1(isum0_0_0_1), .isum0_0_1_0(isum0_0_1_0), .isum0_0_1_1(isum0_0_1_1),
  .isum0_1_0_0(isum0_1_0_0), .isum0_1_0_1(isum0_1_0_1), .isum0_1_1_0(isum0_1_1_0), .isum0_1_1_1(isum0_1_1_1),
  .sum(sum),
  .sum0(sum0),
  .sum0_0(sum0_0), .sum0_1(sum0_1),
  .sum0_0_0(sum0_0_0), .sum0_0_1(sum0_0_1), .sum0_1_0(sum0_1_0), .sum0_1_1(sum0_1_1),
  .reg_sum0_0_0_0(sum0_0_0_0), .reg_sum0_0_0_1(sum0_0_0_1), .reg_sum0_0_1_0(sum0_0_1_0), .reg_sum0_0_1_1(sum0_0_1_1),
  .reg_sum0_1_0_0(sum0_1_0_0), .reg_sum0_1_0_1(sum0_1_0_1), .reg_sum0_1_1_0(sum0_1_1_0), .reg_sum0_1_1_1(sum0_1_1_1)
);

`endif // ADDER_TREE_SVA
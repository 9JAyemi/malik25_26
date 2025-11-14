// SVA for adder_tree_top
// Bind into RTL; concise but checks functionality, latency, and overflow; includes coverage
// synthesis translate_off
bind adder_tree_top adder_tree_top_sva();
// synthesis translate_on

module adder_tree_top_sva;
  localparam int W = `ADDER_WIDTH;

  // past-valid for using $past safely
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // -----------------------
  // Stage-3 input registering (1-cycle latency wrt isum*)
  // -----------------------
  assert property (@(posedge clk) past_valid |-> (sum0_0_0_0 == $past(isum0_0_0_0)));
  assert property (@(posedge clk) past_valid |-> (sum0_0_0_1 == $past(isum0_0_0_1)));
  assert property (@(posedge clk) past_valid |-> (sum0_0_1_0 == $past(isum0_0_1_0)));
  assert property (@(posedge clk) past_valid |-> (sum0_0_1_1 == $past(isum0_0_1_1)));
  assert property (@(posedge clk) past_valid |-> (sum0_1_0_0 == $past(isum0_1_0_0)));
  assert property (@(posedge clk) past_valid |-> (sum0_1_0_1 == $past(isum0_1_0_1)));
  assert property (@(posedge clk) past_valid |-> (sum0_1_1_0 == $past(isum0_1_1_0)));
  assert property (@(posedge clk) past_valid |-> (sum0_1_1_1 == $past(isum0_1_1_1)));

  // -----------------------
  // Combinational adder-tree structure checks (each stage)
  // -----------------------
  // L3 (leaves)
  assert property (@(posedge clk) sum0_0_0 == sum0_0_0_0 + sum0_0_0_1);
  assert property (@(posedge clk) sum0_0_1 == sum0_0_1_0 + sum0_0_1_1);
  assert property (@(posedge clk) sum0_1_0 == sum0_1_0_0 + sum0_1_0_1);
  assert property (@(posedge clk) sum0_1_1 == sum0_1_1_0 + sum0_1_1_1);

  // L2
  assert property (@(posedge clk) sum0_0 == sum0_0_0 + sum0_0_1);
  assert property (@(posedge clk) sum0_1 == sum0_1_0 + sum0_1_1);

  // L1 (root)
  assert property (@(posedge clk) sum0 == sum0_0 + sum0_1);

  // -----------------------
  // Output pipeline/width behavior
  // -----------------------
  // Expected sums (zero-extended to stage widths) from previous cycle inputs
  let z3(input logic [W-1:0] x) = $unsigned({3'b000,x}); // W+3 bits: sum of 8 inputs
  let z2(input logic [W-1:0] x) = $unsigned({2'b00 ,x}); // W+2 bits: sum of 4 inputs

  `ifdef 3_LEVEL_ADDER
    let s8 = z3($past(isum0_0_0_0)) + z3($past(isum0_0_0_1))
           + z3($past(isum0_0_1_0)) + z3($past(isum0_0_1_1))
           + z3($past(isum0_1_0_0)) + z3($past(isum0_1_0_1))
           + z3($past(isum0_1_1_0)) + z3($past(isum0_1_1_1)); // W+3 bits

    // Sum register takes lower W+1 bits of previous cycle's full 8-input sum
    assert property (@(posedge clk) past_valid |-> (sum == s8[W:0]));

    // Also must equal truncated previous cycle's tree root
    assert property (@(posedge clk) past_valid |-> (sum == $past(sum0[W:0])));

    // Coverage: no-overflow and overflow into truncated bits
    cover property (@(posedge clk) past_valid && (s8[W+2:W+1] == 2'b00));
    cover property (@(posedge clk) past_valid && (s8[W+2:W+1] != 2'b00));
  `endif

  `ifdef 2_LEVEL_ADDER
    // Four-input sum (matches RTL's sum0_0 usage)
    let s4 = z2($past(isum0_0_0_0)) + z2($past(isum0_0_0_1))
           + z2($past(isum0_0_1_0)) + z2($past(isum0_0_1_1)); // W+2 bits

    // Sum register takes lower W+1 bits of previous cycle's 4-input sum
    assert property (@(posedge clk) past_valid |-> (sum == s4[W:0]));

    // Also must equal truncated previous cycle's L2 sum0_0
    assert property (@(posedge clk) past_valid |-> (sum == $past(sum0_0[W:0])));

    // Coverage: no-overflow and overflow into truncated bit(s)
    cover property (@(posedge clk) past_valid && (s4[W+1:W] == 2'b00));
    cover property (@(posedge clk) past_valid && (s4[W+1:W] != 2'b00));
  `endif

  // Basic X-prop sanity on outputs each cycle
  assert property (@(posedge clk) !$isunknown(sum));

endmodule
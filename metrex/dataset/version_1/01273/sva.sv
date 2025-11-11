// SVA for top_module
// Bind this module to the DUT and connect a verification clock/reset.
// Example: bind top_module top_module_sva u_top_module_sva(.clk(tb_clk), .rst_n(tb_rst_n), .*);

module top_module_sva (
  input logic              clk,
  input logic              rst_n,
  // DUT ports (as inputs to SVA module)
  input logic [3:0]        A,
  input logic [3:0]        B,
  input logic              C,
  input logic [3:0]        D,
  input logic              eq,
  input logic              gt,
  input logic [3:0]        final_output
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Helpers
  let shamt      = D[1:0];
  let exp_shift  = (C == 1'b0) ? (A << shamt) : (A >> shamt);
  let exp_final  = ((A == B) ? exp_shift : 4'b0000);

  // Environment sanity (avoid X/Z on inputs)
  assume property (!$isunknown({A,B,C,D}));

  // Basic functional correctness
  assert property (eq == (A == B));
  assert property (gt == (A > B));
  assert property (final_output == exp_final);

  // Outputs must be known (given known inputs)
  assert property (!$isunknown({eq,gt,final_output}));

  // Mutual exclusivity (redundant but tight)
  assert property (!(eq && gt));

  // Final output gating by equality
  assert property ((A != B) |-> (final_output == 4'b0000));
  assert property ((A == B) |-> (final_output == exp_shift));

  // Pure combinational: outputs stable if all inputs stable
  assert property ($stable({A,B,C,D}) |-> $stable({eq,gt,final_output}));

  // Insensitivity to unused D[3:2] bits
  assert property ($stable({A,B,C,D[1:0]}) && $changed(D[3:2]) |-> $stable({eq,gt,final_output}));

  // Minimal but meaningful coverage
  cover property ((A == B) && eq && (final_output == exp_shift));     // equality passthrough case
  cover property ((A != B) && !eq && (final_output == 4'b0000));      // gated-to-zero case
  cover property (gt && (A > B));                                     // greater-than observed
  cover property (!gt && (A <= B));                                   // non-greater observed

  // Cover both shift directions when enabled (eq)
  cover property ((A == B) && (C == 1'b0));                           // left shift path
  cover property ((A == B) && (C == 1'b1));                           // right shift path

  // Exercise all shift amounts (when eq holds so output is observable)
  cover property ((A == B) && (D[1:0] == 2'd0));
  cover property ((A == B) && (D[1:0] == 2'd1));
  cover property ((A == B) && (D[1:0] == 2'd2));
  cover property ((A == B) && (D[1:0] == 2'd3));

  // Boundary value coverage for A/B
  cover property (A == 4'h0 && B == 4'h0);
  cover property (A == 4'hF && B == 4'hF);
  cover property (A == 4'hF && B == 4'h0); // gt true
  cover property (A == 4'h0 && B == 4'hF); // lt case

  // Demonstrate D[3:2] insensitivity in operation
  sequence d_high_bits_toggle;
    $stable({A,B,C,D[1:0]}) ##1 $changed(D[3:2]);
  endsequence
  cover property (d_high_bits_toggle && $stable({eq,gt,final_output}));

endmodule
// SVA for top_module. Bind this into the DUT and drive clk/rst_n from your TB.
module top_module_sva #(parameter WIDTH=8) (
  input logic clk,
  input logic rst_n
);
  // This module is bound into top_module instance; DUT signals are visible here.

  default clocking cb @ (posedge clk); endclocking
  default disable iff (!rst_n);

  // Golden unsigned reference (no carry-in)
  logic [WIDTH:0] ref_sum;
  assign ref_sum = {1'b0, a} + {1'b0, b};

  // Basic X/Z sanitation
  assert property (!$isunknown({a,b})) |-> (!$isunknown({s,overflow})));

  // Local generate/propagate definitions
  assert property (g == (a & b));
  assert property (p == (a ^ b));

  // and_module output consistent with internal g
  assert property (c == g);

  // Carry chain
  assert property (carry[0] == g[0]);
  genvar i;
  generate
    for (i = 1; i < WIDTH; i++) begin : a_carry_chain
      assert property (carry[i] == (g[i] | (p[i] & carry[i-1])));
    end
  endgenerate

  // Sum bit correctness w.r.t. propagate and incoming carry
  assert property (sum[0] == p[0]);
  generate
    for (i = 1; i < WIDTH; i++) begin : a_sum_bits
      assert property (sum[i] == (p[i] ^ carry[i-1]));
    end
  endgenerate

  // Output mapping
  assert property (s == sum);

  // End-to-end arithmetic checks (unsigned add, no carry-in)
  assert property (s == ref_sum[WIDTH-1:0]);
  assert property (carry[WIDTH-1] == ref_sum[WIDTH]);  // chain carry-out matches golden carry-out
  assert property (overflow == ref_sum[WIDTH]);        // overflow should be final carry-out
  assert property (overflow == carry[WIDTH-1]);        // and must match chain carry[7]

  // Minimal functional coverage
  cover property (ref_sum[WIDTH]);                                // overflow seen
  cover property (!ref_sum[WIDTH] && (s == '0));                  // zero result without overflow
  cover property ({a,b} == {WIDTH{1'b0}, {WIDTH{1'b1}}});         // 0 + all-1s
  cover property ({a,b} == {{WIDTH{1'b1}}, {WIDTH{1'b1}}});       // all-1s + all-1s
  cover property (a == 8'h55 && b == 8'haa);                      // alternating bits
  cover property (a == 8'h80 && b == 8'h80 && !ref_sum[WIDTH]);   // signed overflow pattern (carry-out 0)
endmodule

// Example bind (connect clk/rst_n from your TB):
// bind top_module top_module_sva sva_top (.clk(tb_clk), .rst_n(tb_rst_n));
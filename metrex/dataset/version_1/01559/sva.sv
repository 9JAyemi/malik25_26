// SVA for shift_reg_comb
// Bindable checker that reaches internal signals for strong end-to-end checks

module shift_reg_comb_sva (
  input logic        clk,
  input logic        d,
  input logic [3:0]  in,
  input logic        out_and,
  input logic        out_or,
  input logic        out_xor,
  input logic [7:0]  sum,
  input logic [2:0]  shift_reg, // internal
  input logic        q          // internal
);

  default clocking cb @(posedge clk); endclocking

  // Combinational function correctness (sampled each clk)
  assert property (out_and == ((in[0] & in[1]) | (in[2] & in[3])));
  assert property (out_or  == ((in[0] | in[1]) & (in[2] | in[3])));
  assert property (out_xor == ((in[0] ^ in[1]) & (in[2] ^ in[3])));

  // Shift-register pipeline behavior
  // 1-cycle vector shift
  assert property (##1 (shift_reg == { $past(shift_reg[1:0],1), $past(d,1) }));
  // 3-cycle delay from d to q
  assert property (##3 (q == $past(d,3)));

  // Sum construction and range
  // Exact arithmetic equivalence (8-bit operands)
  assert property (sum == ({5'b0, shift_reg} + {5'b0, out_and, out_or, out_xor}));
  // Upper nibble must be zero (max sum is 14)
  assert property (sum[7:4] == 4'b0000);
  // Lower nibble equivalence form
  assert property (sum[3:0] == ({1'b0, shift_reg} + {1'b0, out_and, out_or, out_xor}));

  // Basic functional coverage
  // Shift pipeline covers: drive 3 ones then q=1; 3 zeros then q=0
  cover property ((d==1'b1)[*3] ##1 (q==1'b1));
  cover property ((d==1'b0)[*3] ##1 (q==1'b0));
  // Output combinations extremes
  cover property ({out_and,out_or,out_xor} == 3'b000);
  cover property ({out_and,out_or,out_xor} == 3'b111);
  // Sum extremes
  cover property (sum == 8'h00);
  cover property (sum == 8'h0E);
  // Toggle coverage
  cover property ($rose(q));   cover property ($fell(q));
  cover property ($rose(out_and)); cover property ($fell(out_and));
  cover property ($rose(out_or));  cover property ($fell(out_or));
  cover property ($rose(out_xor)); cover property ($fell(out_xor));

endmodule

// Bind into each instance of the DUT to access internals
bind shift_reg_comb shift_reg_comb_sva u_shift_reg_comb_sva (
  .clk       (clk),
  .d         (d),
  .in        (in),
  .out_and   (out_and),
  .out_or    (out_or),
  .out_xor   (out_xor),
  .sum       (sum),
  .shift_reg (shift_reg),
  .q         (q)
);
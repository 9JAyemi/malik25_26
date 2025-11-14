// SVA for top_module
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic [7:0]  a_sync,
  input logic [7:0]  b_sync,
  input logic [7:0]  sum,
  input logic [7:0]  carry
);

  default clocking cb @(posedge clk); endclocking

  // Track valid past
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Reset behavior: flops clear on cycle after reset seen high
  assert property (cb (past_valid && $past(reset)) |-> (a_sync==8'h00 && b_sync==8'h00));

  // Flop sampling: when not in or entering reset
  assert property (cb (past_valid && !reset && !$past(reset)) |-> (a_sync==$past(a) && b_sync==$past(b)));

  // No X on key nets when not in reset
  assert property (cb (past_valid && !reset) |-> !$isunknown({a_sync,b_sync,sum,carry}));

  // Adder correctness (9-bit sum)
  assert property (cb {carry[7], sum} == ({1'b0,a_sync} + {1'b0,b_sync}));

  // Bitwise sum/carry equations and chain connectivity
  // LSB (Cin=0)
  assert property (cb sum[0]   == (a_sync[0] ^ b_sync[0]));
  assert property (cb carry[0] == (a_sync[0] & b_sync[0]));
  // Bits 1..7
  genvar i;
  generate
    for (i=1; i<8; i++) begin : G_BITWISE
      assert property (cb sum[i]   == (a_sync[i] ^ b_sync[i] ^ carry[i-1]));
      assert property (cb carry[i] == ((a_sync[i] & b_sync[i]) | (carry[i-1] & (a_sync[i] ^ b_sync[i]))));
    end
  endgenerate

  // During reset, outputs reflect zeros
  assert property (cb reset |-> (sum==8'h00 && carry==8'h00));

  // Key functional coverage
  // 1) Overflow occurs
  cover property (cb (!reset && carry[7]));
  // 2) No-carry addition (all carries zero)
  cover property (cb (!reset && carry==8'h00));
  // 3) Full ripple through chain (FF + 01 => overflow, sum wraps)
  cover property (cb (!reset && a_sync==8'hFF && b_sync==8'h01 && carry[7] && sum==8'h00));
  // 4) Alternating bits, no carries (AA + 55)
  cover property (cb (!reset && a_sync==8'hAA && b_sync==8'h55 && carry==8'h00 && sum==8'hFF));
  // 5) Reset deassert observed
  cover property (cb (past_valid && $past(reset) && !reset));

endmodule

// Bind into DUT
bind top_module top_module_sva sva (
  .clk    (clk),
  .reset  (reset),
  .a      (a),
  .b      (b),
  .a_sync (a_sync),
  .b_sync (b_sync),
  .sum    (sum),
  .carry  (carry)
);
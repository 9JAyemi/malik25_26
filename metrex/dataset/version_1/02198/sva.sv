// SVA for a23_multiply
// Focus: functional correctness, control sequencing, flags, and simple coverage.

module a23_multiply_sva (
  input  logic         i_clk,
  input  logic         i_rst,
  input  logic [31:0]  i_a_in,
  input  logic [31:0]  i_b_in,
  input  logic  [1:0]  i_function,
  input  logic         i_execute,
  input  logic [31:0]  o_out,
  input  logic  [1:0]  o_flags,
  input  logic         o_done,

  // Internal DUT signals
  input  logic [31:0]  product,
  input  logic  [3:0]  count,
  input  logic         enable,
  input  logic         accumulate
);

  default clocking cb @(posedge i_clk); endclocking

  // Basic connectivity/encoding
  assert property (enable     == i_function[0]);
  assert property (accumulate == i_function[1]);
  assert property (o_out == product);
  assert property (o_flags[1] == o_out[31]);          // sign
  assert property (o_flags[0] == (o_out == 32'd0));   // zero
  assert property (o_done == 1'b1);

  // Reset behavior (check at clock edge)
  assert property (i_rst |-> (product == 32'd0 && count == 4'd0));

  // When enable is 0, next cycle product/count clear
  assert property (disable iff (i_rst)
                   !enable |=> (product == 32'd0 && count == 4'd0));

  // When enable stays asserted, count increments by 1 (mod 16)
  assert property (disable iff (i_rst)
                   enable |=> (enable -> count == $past(count) + 4'd1));

  // Explicit wrap check 15 -> 0 when enable holds
  assert property (disable iff (i_rst)
                   (enable && count == 4'hF) |=> (enable -> count == 4'h0));

  // Multiply write on count==0 when executing (truncated to 32b)
  assert property (disable iff (i_rst)
    (enable && i_execute && count == 4'd0)
      |=> (enable -> product == ( ($unsigned($past(i_a_in)) * $unsigned($past(i_b_in))) [31:0] )));

  // Accumulate write on count==3 when executing and accumulate set (truncated to 32b)
  assert property (disable iff (i_rst)
    (enable && i_execute && accumulate && count == 4'd3)
      |=> (enable -> product == ( ($unsigned($past(product)) + $unsigned($past(i_a_in))) [31:0] )));

  // No unintended product change when no write conditions hit (while enable holds)
  assert property (disable iff (i_rst)
    (enable &&
     !(i_execute && count == 4'd0) &&
     !(i_execute && accumulate && count == 4'd3))
      |=> (enable -> product == $past(product)));

  // Simple functional coverage
  cover property (disable iff (i_rst) enable && i_execute && count == 4'd0);      // multiply event
  cover property (disable iff (i_rst) enable && i_execute && accumulate && count == 4'd3); // accumulate event
  cover property (disable iff (i_rst) enable && count == 4'hF ##1 enable && count == 4'h0); // wrap
  cover property (disable iff (i_rst) o_flags[0] == 1'b1); // zero flag seen
  cover property (disable iff (i_rst) o_flags[1] == 1'b1); // sign flag seen
  cover property (disable iff (i_rst) !enable ##1 (product == 32'd0 && count == 4'd0));    // clear on disable

endmodule

// Bind into DUT
bind a23_multiply a23_multiply_sva sva_i (
  .i_clk(i_clk),
  .i_rst(i_rst),
  .i_a_in(i_a_in),
  .i_b_in(i_b_in),
  .i_function(i_function),
  .i_execute(i_execute),
  .o_out(o_out),
  .o_flags(o_flags),
  .o_done(o_done),
  .product(product),
  .count(count),
  .enable(enable),
  .accumulate(accumulate)
);
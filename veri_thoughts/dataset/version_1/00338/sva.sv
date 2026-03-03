// SVA for concat_8bit
module concat_8bit_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  input  logic        ctrl,
  input  logic [15:0] out
);

  // Inputs must be known when sampled for update
  assert property (@(posedge clk) disable iff (reset)
                   !$isunknown({a,b,ctrl}));

  // Reset behavior: output forced to 0 while reset asserted
  assert property (@(posedge clk) reset |-> out==16'h0000);
  // After a synchronous falling edge of reset, out is still 0 at that clock
  assert property (@(posedge clk) $fell(reset) |-> out==16'h0000);

  // Functional update: next-cycle out equals concatenation per ctrl
  assert property (@(posedge clk) disable iff (reset)
                   1'b1 |-> ##1 (reset || out == (ctrl ? {a,b} : {b,a})));

  // Byte-level mapping (redundant but precise)
  assert property (@(posedge clk) disable iff (reset)
                   ctrl |-> ##1 (reset || (out[15:8]==$past(a) && out[7:0]==$past(b))));
  assert property (@(posedge clk) disable iff (reset)
                   !ctrl |-> ##1 (reset || (out[15:8]==$past(b) && out[7:0]==$past(a))));

  // Out should be known starting the second non-reset cycle after deassertion
  assert property (@(posedge clk)
                   (!reset && !$past(reset)) |-> !$isunknown(out));

  // Coverage: exercise both concatenation orders and control toggling
  cover property (@(posedge clk) disable iff (reset)
                  ctrl ##1 (!reset && out=={$past(a),$past(b)}));
  cover property (@(posedge clk) disable iff (reset)
                  !ctrl ##1 (!reset && out=={$past(b),$past(a)}));
  cover property (@(posedge clk) disable iff (reset)
                  ctrl ##1 !ctrl ##1 ctrl);

  // Reset activity coverage
  cover property (@(posedge clk) $rose(reset));
  cover property (@(posedge clk) $fell(reset));

endmodule

// Bind SVA to DUT
bind concat_8bit concat_8bit_sva u_concat_8bit_sva (.*);
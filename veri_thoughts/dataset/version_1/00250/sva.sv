// SVA for binary_counter
module binary_counter_sva #(parameter WIDTH=4)
(
  input logic              clk,
  input logic              rst,
  input logic              en,
  input logic [WIDTH-1:0]  out
);

  bit started;
  initial started = 1'b0;
  always @(posedge clk) started <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Core next-state functional equivalence (covers reset, hold, increment, wrap)
  assert property (disable iff (!started)
    out == ( $past(rst) ? {WIDTH{1'b0}}
           : ($past(en) ? $past(out) + 1'b1
                        : $past(out) ) )
  );

  // Optional sanity: output never X/Z once running
  assert property (disable iff (!started) !$isunknown(out));

  // Coverage: exercise all branches and wrap
  cover property (disable iff (!started) $past(rst) && (out == {WIDTH{1'b0}}));                      // reset branch
  cover property (disable iff (!started) !$past(rst) && !$past(en) && (out == $past(out)));          // hold branch
  cover property (disable iff (!started) !$past(rst) && $past(en) &&
                                   ($past(out) != {WIDTH{1'b1}}) && (out == $past(out) + 1'b1));     // increment (no wrap)
  cover property (disable iff (!started) !$past(rst) && $past(en) &&
                                   ($past(out) == {WIDTH{1'b1}}) && (out == {WIDTH{1'b0}}));         // wrap 15->0
  cover property (disable iff (!started) $past(rst) && $past(en) && (out == {WIDTH{1'b0}}));         // rst wins over en

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva #(.WIDTH(4)) i_binary_counter_sva
(
  .clk(clk),
  .rst(rst),
  .en(en),
  .out(out)
);
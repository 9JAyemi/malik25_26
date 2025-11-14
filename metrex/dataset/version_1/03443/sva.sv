// SVA for counter16: concise, high-quality checks + coverage
module counter16_sva(input logic clk, rst, input logic [15:0] count);

  // Track that we have at least one prior cycle for $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z after time 0
  assert property (past_valid |-> !$isunknown(rst));
  assert property (past_valid |-> !$isunknown(count));

  // Synchronous reset: next cycle must be zero
  assert property (rst |=> count == 16'd0);

  // While reset is held, count stays at zero
  assert property (rst && $past(rst) |-> count == 16'd0);

  // Increment when not resetting and not at max
  assert property (disable iff (!past_valid)
                   (!rst && count != 16'hFFFF) |=> count == $past(count) + 16'd1);

  // Wrap from max to zero when not resetting
  assert property (disable iff (!past_valid)
                   (!rst && count == 16'hFFFF) |=> count == 16'd0);

  // Any zero without reset must be due to wrap
  assert property (disable iff (!past_valid)
                   (!rst && count == 16'd0) |-> ($past(rst) || $past(count) == 16'hFFFF));

  // Coverage: reset behavior
  cover property (rst ##1 count == 16'd0);

  // Coverage: normal increment
  cover property (disable iff (!past_valid)
                  (!rst && count != 16'hFFFF) ##1 count == $past(count) + 16'd1);

  // Coverage: wrap-around event
  cover property (disable iff (!past_valid)
                  (!rst && count == 16'hFFFF) ##1 count == 16'd0);

endmodule

// Bind into the DUT
bind counter16 counter16_sva u_counter16_sva (.clk(clk), .rst(rst), .count(count));
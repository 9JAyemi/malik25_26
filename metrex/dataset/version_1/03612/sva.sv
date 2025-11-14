// SVA checker for up_counter
module up_counter_sva (
  input logic       clk,
  input logic       reset,
  input logic [2:0] count_out
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (!$isunknown(reset));
  assert property (!$isunknown(count_out));

  // Reset behavior
  // If reset was asserted last cycle, counter must read 0 now
  assert property ($past(reset) |-> (count_out == 3'd0));
  // While reset is held across cycles, hold at 0 and stable
  assert property ($past(reset) && reset |-> (count_out == 3'd0 && $stable(count_out)));

  // Functional increment (mod-8) when not in reset
  assert property (disable iff (reset)
                   count_out == $past(count_out) + 3'd1);

  // Coverage
  // One full lap without reset: 0->1->...->7->0
  cover property (disable iff (reset)
                  count_out==3'd0 ##1 count_out==3'd1 ##1 count_out==3'd2 ##1 count_out==3'd3
                  ##1 count_out==3'd4 ##1 count_out==3'd5 ##1 count_out==3'd6 ##1 count_out==3'd7
                  ##1 count_out==3'd0);

  // See reset clear the counter from a non-zero value
  cover property (count_out!=3'd0 ##1 reset ##1 count_out==3'd0);
endmodule

// Bind into DUT
bind up_counter up_counter_sva up_counter_sva_i(.clk(clk), .reset(reset), .count_out(count_out));
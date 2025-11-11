// SVA for binary_counter
module binary_counter_sva (
  input logic       clk,
  input logic       reset,
  input logic       enable,
  input logic [3:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Track availability of a past sample
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset behavior: next cycle must be 0 (regardless of enable)
  assert property ( reset |=> (count == 4'h0) );

  // Hold when not enabled
  assert property ( disable iff (reset) (!enable) |=> $stable(count) );

  // Increment when enabled and not at max
  assert property ( disable iff (reset) (enable && count != 4'hF) |=> (count == $past(count) + 4'd1) );

  // Wrap when enabled at max
  assert property ( disable iff (reset) (enable && count == 4'hF) |=> (count == 4'h0) );

  // Any change must be due to enable or reset
  assert property ( disable iff (!past_valid) (count != $past(count)) |-> (reset || $past(enable)) );

  // Any change must match increment-or-wrap function
  assert property ( disable iff (!past_valid || reset)
                    (count != $past(count))
                    |-> (count == (($past(count) == 4'hF) ? 4'h0 : $past(count) + 4'd1)) );

  // No X/Z on output
  assert property ( !$isunknown(count) );

  // Coverage
  cover property ( reset ##1 (count == 4'h0) );                           // reset to zero
  cover property ( disable iff (reset) (enable && count != 4'hF) ##1 (count == $past(count) + 4'd1) ); // increment
  cover property ( disable iff (reset) (enable && count == 4'hF) ##1 (count == 4'h0) );                // wrap
  cover property ( disable iff (reset) (!enable) ##1 $stable(count) );                                 // hold
  cover property ( disable iff (reset) (enable[*16]) ##0 (count == $past(count,16)) );                 // full 16-step cycle

endmodule

bind binary_counter binary_counter_sva u_binary_counter_sva (
  .clk(clk),
  .reset(reset),
  .enable(enable),
  .count(count)
);
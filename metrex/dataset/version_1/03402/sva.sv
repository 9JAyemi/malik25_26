// SVA for counter
module counter_sva (
  input logic        clk,
  input logic [3:0]  reset,
  input logic [3:0]  load,
  input logic [3:0]  increment,
  input logic [3:0]  count
);

  // Clocking and past-valid guard
  default clocking cb @(posedge clk); endclocking
  bit past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Reset dominates: next count is 0 when reset==4'hF
  assert property ( $past(reset == 4'hF) |-> (count == 4'h0) );

  // Load takes effect when not in reset and load!=0
  assert property ( $past(reset != 4'hF && load != 4'h0) |-> (count == $past(load)) );

  // Increment path (mod-16) when not in reset and load==0
  assert property ( $past(reset != 4'hF && load == 4'h0)
                    |-> (count == (($past(count) + $past(increment)) & 4'hF)) );

  // Increment==0 holds value on increment path
  assert property ( $past(reset != 4'hF && load == 4'h0 && increment == 4'h0)
                    |-> (count == $past(count)) );

  // Increment!=0 changes value on increment path (mod-16)
  assert property ( $past(reset != 4'hF && load == 4'h0 && increment != 4'h0)
                    |-> (count != $past(count)) );

  // Explicitly check reset priority over load
  assert property ( $past(reset == 4'hF && load != 4'h0) |-> (count == 4'h0) );

  // No X/Z on count after first cycle
  assert property ( !$isunknown(count) );

  // Coverage: hit each behavior and a wrap-around increment
  cover property ( $past(reset == 4'hF) && (count == 4'h0) );

  cover property ( $past(reset != 4'hF && load != 4'h0) && (count == $past(load)) );

  cover property ( $past(reset != 4'hF && load == 4'h0 && increment != 4'h0)
                   && (count == (($past(count) + $past(increment)) & 4'hF)) );

  // Wrap-around when carry out occurs
  cover property ( $past(reset != 4'hF && load == 4'h0) &&
                   (($past(count) + $past(increment)) > 4'hF) );

  // Two consecutive increment cycles
  cover property ( (reset != 4'hF && load == 4'h0 && increment != 4'h0)
                   ##1 (reset != 4'hF && load == 4'h0 && increment != 4'h0) );

endmodule

// Bind into DUT
bind counter counter_sva i_counter_sva(
  .clk(clk),
  .reset(reset),
  .load(load),
  .increment(increment),
  .count(count)
);
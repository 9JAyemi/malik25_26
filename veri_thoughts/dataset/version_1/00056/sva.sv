// SVA for up_down_counter
module up_down_counter_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        mode,
  input  logic [3:0]  initial_value,
  input  logic [3:0]  counter_value
);

  default clocking cb @(posedge clk); endclocking

  // Make $past safe from time 0
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  localparam logic [3:0] MAX  = 4'hF;
  localparam logic [3:0] ZERO = 4'h0;

  // No X/Z on key signals
  assert property ( !$isunknown({reset, mode, initial_value, counter_value}) );

  // Reset behavior: next cycle counter equals prior initial_value
  assert property ( past_valid && $past(reset) |-> counter_value == $past(initial_value) );

  // Count up (no wrap)
  assert property ( past_valid && !$past(reset) && $past(mode==1'b0) &&
                    $past(counter_value != MAX)
                    |-> counter_value == $past(counter_value) + 1 );

  // Count up (wrap 15->0)
  assert property ( past_valid && !$past(reset) && $past(mode==1'b0) &&
                    $past(counter_value == MAX)
                    |-> counter_value == ZERO );

  // Count down (no wrap)
  assert property ( past_valid && !$past(reset) && $past(mode==1'b1) &&
                    $past(counter_value != ZERO)
                    |-> counter_value == $past(counter_value) - 1 );

  // Count down (wrap 0->15)
  assert property ( past_valid && !$past(reset) && $past(mode==1'b1) &&
                    $past(counter_value == ZERO)
                    |-> counter_value == MAX );

  // Must change every active cycle (no stall when not in reset)
  assert property ( past_valid && !$past(reset) |-> counter_value != $past(counter_value) );

  // Functional coverage
  cover property ( past_valid && $past(reset) && counter_value == $past(initial_value) );
  cover property ( past_valid && !$past(reset) && $past(mode==1'b0) &&
                   $past(counter_value != MAX) && counter_value == $past(counter_value)+1 );
  cover property ( past_valid && !$past(reset) && $past(mode==1'b0) &&
                   $past(counter_value == MAX) && counter_value == ZERO );
  cover property ( past_valid && !$past(reset) && $past(mode==1'b1) &&
                   $past(counter_value != ZERO) && counter_value == $past(counter_value)-1 );
  cover property ( past_valid && !$past(reset) && $past(mode==1'b1) &&
                   $past(counter_value == ZERO) && counter_value == MAX );

endmodule

// Bind into DUT
bind up_down_counter up_down_counter_sva sva_up_down_counter (
  .clk(clk),
  .reset(reset),
  .mode(mode),
  .initial_value(initial_value),
  .counter_value(counter_value)
);
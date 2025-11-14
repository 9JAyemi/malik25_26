// SVA for deserializer
module deserializer_sva #(
  parameter int BITS = 32,
  parameter int BITS_COUNTER = 8
)(
  input logic                     clk,
  input logic                     reset,
  input logic                     enable,
  input logic                     in,
  input logic [BITS_COUNTER-1:0]  framesize,
  input logic [BITS-1:0]          out,
  input logic                     complete,
  input logic [BITS_COUNTER-1:0]  counter
);

  default clocking cb @(posedge clk); endclocking

  // Complete reflects equality
  assert property (complete == (counter == framesize));

  // Reset clears state
  assert property (reset |=> (counter == '0 && out == '0));

  // Framesize must be legal
  assert property (framesize <= BITS);

  // No OOB index when capturing
  assert property ((enable && !complete) |-> (counter < BITS));

  // Counter updates exactly when capturing
  assert property (disable iff (reset)
                   (enable && !complete) |=> counter == $past(counter) + 1);

  // Hold when not capturing
  assert property (disable iff (reset)
                   (!enable || complete) |=> (counter == $past(counter) && $stable(out)));

  // Captured bit equals sampled input
  assert property (disable iff (reset)
                   (enable && !complete) |=> out[$past(counter)] == $past(in));

  // Complete rises only after last increment to match framesize
  assert property (disable iff (reset)
                   $rose(complete) |-> $past(enable && !$past(complete) &&
                                             ($past(counter)+1) == $past(framesize)));

  // Framesize stable while a transfer is in progress
  assert property (disable iff (reset) (!complete) |-> $stable(framesize));

  // Progress: under steady enable and stable framesize, complete within BITS cycles
  assert property (disable iff (reset)
                   (enable && !complete && $stable(framesize) && (framesize <= BITS))
                   |-> ((enable until_with $rose(complete)) and ##[0:BITS] $rose(complete)));

  // Coverage
  cover property (reset ##1 !reset ##1 (enable && !complete) ##[1:BITS] $rose(complete));
  cover property (framesize == 0 && complete);
  cover property (framesize == BITS && $rose(complete));
  cover property (disable iff (reset) (enable && !complete && counter == 0));
  cover property (disable iff (reset) (enable && !complete && counter == framesize-1));

endmodule

// Bind into DUT
bind deserializer deserializer_sva #(.BITS(BITS), .BITS_COUNTER(BITS_COUNTER)) deserializer_sva_i (.*);
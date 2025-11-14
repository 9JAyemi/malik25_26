// SVA for pulse_generator
module pulse_generator_sva #(
  parameter int PULSE_DURATION   = 100,
  parameter int CLOCK_FREQUENCY  = 50
)(
  input  logic        clk,
  input  logic        reset,
  input  logic        start,
  input  logic        pulse,
  input  logic [31:0] count,
  input  logic        pulse_on
);
  localparam int unsigned PULSE_CYCLES = PULSE_DURATION * CLOCK_FREQUENCY;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic sanity
  assert property (!$isunknown({pulse,pulse_on,count})));
  assert property (pulse == pulse_on);

  // Reset behavior (must check even when reset=1)
  assert property (disable iff (1'b0) reset |=> (count==0 && !pulse && !pulse_on));

  // Start behavior: restart pulse and counter
  assert property (start |=> (count==0 && pulse && pulse_on));

  // Counting while active (no start): increment and keep pulse high until limit
  assert property ((!start && (count < PULSE_CYCLES)) |=> (count == $past(count)+1 && pulse && pulse_on));

  // Stop at/after limit (no start): drop pulse, hold counter
  assert property ((!start && (count >= PULSE_CYCLES)) |=> (!pulse && !pulse_on && $stable(count)));

  // Exact pulse length when no restart: PULSE_CYCLES+1 highs then a low
  assert property ($rose(start) |=> ( (pulse [* (PULSE_CYCLES+1)]) ##1 !pulse )
                                      intersect (!start [* (PULSE_CYCLES+1)]));

  // Coverage
  // Single pulse with no restart: see exact length then drop
  cover property ($rose(start) |=> ( (pulse [* (PULSE_CYCLES+1)]) ##1 !pulse )
                                   intersect (!start [* (PULSE_CYCLES+1)]));
  // Restart during active window
  cover property ($rose(start) ##[1:PULSE_CYCLES] $rose(start));
  // Reset during active pulse
  cover property ($rose(start) ##[1:PULSE_CYCLES] reset);

endmodule

// Bind into DUT
bind pulse_generator pulse_generator_sva #(
  .PULSE_DURATION  (PULSE_DURATION),
  .CLOCK_FREQUENCY (CLOCK_FREQUENCY)
) pulse_generator_sva_i (
  .clk,
  .reset,
  .start,
  .pulse,
  .count,
  .pulse_on
);
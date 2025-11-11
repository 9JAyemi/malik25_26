// SVA checker for error2
module error2_sva
  #(parameter int unsigned TERMINAL = 20'd1000000,
    parameter int unsigned PERIOD   = TERMINAL+1)
(
  input logic              clk,
  input logic [1:0]        leds,
  input logic [19:0]       counter
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default disable iff (!past_valid || $isunknown({counter,leds}))

  // Counter stays within 0..TERMINAL
  assert property (counter inside {[20'd0:TERMINAL]});

  // Counter next-state behavior
  assert property (counter != TERMINAL |=> counter == $past(counter)+20'd1);
  assert property (counter == TERMINAL |=> counter == 20'd0);

  // LEDs toggle only on wrap, and invert exactly
  assert property (counter == TERMINAL |=> leds == ~$past(leds));
  assert property (counter != TERMINAL |=> leds == $past(leds));
  assert property ($changed(leds) |-> counter == TERMINAL);

  // Wrap-to-wrap period is exactly PERIOD cycles
  assert property (counter == TERMINAL |=> ##PERIOD (counter == TERMINAL));

  // Coverage
  cover property (counter == TERMINAL);                         // saw a wrap
  cover property (counter == TERMINAL ##1 leds != $past(leds)); // leds toggled on wrap
  cover property (counter == TERMINAL ##PERIOD counter == TERMINAL); // two wraps seen

endmodule

// Bind into DUT
bind error2 error2_sva i_error2_sva (.clk(clk), .leds(leds), .counter(counter));
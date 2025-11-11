// SVA for pwm_generator
module pwm_generator_sva #(parameter int TERM = 16000) (
  input logic        Clk,
  input logic        Reset,
  input logic [3:0]  DutyCycle,
  input logic        PWM,
  input logic [15:0] counter
);

  default clocking cb @(posedge Clk); endclocking

  // Reset behavior (synchronous)
  property p_reset_clears; @(posedge Clk) Reset |=> (counter==16'd0 && PWM==1'b0); endproperty
  assert property (p_reset_clears);

  // No X after reset deasserts
  assert property (disable iff (Reset) !$isunknown({counter,PWM}));

  // Counter stays in range
  assert property (disable iff (Reset) (counter <= TERM));

  // Counter increments when not at terminal
  assert property (disable iff (Reset) (counter != TERM) |=> counter == $past(counter) + 16'd1);

  // Rollover on terminal count
  assert property (disable iff (Reset) (counter == TERM) |=> counter == 16'd0);

  // PWM updates only on rollover with specified equation (as coded)
  assert property (disable iff (Reset) (counter == TERM) |=> PWM == ($past(counter) < DutyCycle));

  // Otherwise PWM holds its previous value
  assert property (disable iff (Reset) (counter != TERM) |=> PWM == $past(PWM));

  // Simple period cover: 0 -> TERM -> 0
  cover property (disable iff (Reset) (counter==16'd0) ##[1:TERM] (counter==TERM) ##1 (counter==16'd0));

  // Rollover is observed
  cover property (disable iff (Reset) (counter == TERM));

  // Try to see PWM go high at rollover (should expose issues if never hits)
  cover property (disable iff (Reset) (counter == TERM) |=> PWM == 1'b1);

  // Corner duty settings at rollover
  cover property (disable iff (Reset) (counter == TERM && DutyCycle == 4'd0));
  cover property (disable iff (Reset) (counter == TERM && DutyCycle == 4'd15));

  // Any PWM transition (should occur if PWM ever changes)
  cover property (disable iff (Reset) $changed(PWM));

endmodule

// Bind into DUT (example)
// bind pwm_generator pwm_generator_sva #(.TERM(16000))
//   pwm_sva_i (.Clk(Clk), .Reset(Reset), .DutyCycle(DutyCycle), .PWM(PWM), .counter(counter));
// SVA for myModule: concise, high-quality checks and coverage
module myModule_sva (
  input logic        CLOCK_50,
  input logic        signal,
  input logic [24:0] counter
);

  default clocking cb @(posedge CLOCK_50); endclocking

  bit past_valid;
  always @(posedge CLOCK_50) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Normal counting: when previous counter != 10, counter increments and signal holds
  assert property ( ($past(counter) != 25'd10)
                    |-> (counter == $past(counter) + 25'd1 && signal == $past(signal)) );

  // Hit-10 behavior: on previous counter == 10, counter resets to 0 and signal toggles
  assert property ( ($past(counter) == 25'd10)
                    |-> (counter == 25'd0 && signal == ~$past(signal)) );

  // Signal changes only on 10
  assert property ( $changed(signal) |-> ($past(counter) == 25'd10) );

  // Toggle periodicity: exactly every 11 cycles (stable for 10, toggle on 11th)
  assert property ( $changed(signal) |=> $stable(signal)[*10] ##1 $changed(signal) );

  // Coverage: observe toggle event (10 -> 0 with signal change)
  cover property ( ($past(counter) == 25'd10) && (counter == 25'd0) && $changed(signal) );

  // Coverage: both polarities of toggle occur
  cover property ( $rose(signal) );
  cover property ( $fell(signal) );

  // Coverage: consecutive toggles separated by 11 cycles
  cover property ( $changed(signal) ##11 $changed(signal) );

endmodule

bind myModule myModule_sva sva_inst(
  .CLOCK_50(CLOCK_50),
  .signal   (signal),
  .counter  (counter)
);
// SVA for clock_gate
module clock_gate_sva (input logic CLK, EN, TE, ENCLK);

  // Use the functional clock for sampling
  default clocking cb @(posedge CLK); endclocking

  // Core functional relation (registered): ENCLK mirrors ~EN from the previous cycle
  assert property ( !$isunknown($past(EN)) |-> ENCLK == ~ $past(EN) );

  // Output never goes X/Z at sampling points
  assert property ( ! $isunknown(ENCLK) );

  // Any ENCLK edge can only occur while CLK is high (i.e., right after posedge CLK)
  assert property ( @(posedge ENCLK or negedge ENCLK) CLK );

  // Coverage
  cover property ( EN==0 ##1 ENCLK==1 ); // enable low drives ENCLK high next cycle
  cover property ( EN==1 ##1 ENCLK==0 ); // enable high drives ENCLK low next cycle
  cover property ( $rose(ENCLK) );
  cover property ( $fell(ENCLK) );
  cover property ( $rose(TE) );
  cover property ( $fell(TE) );

endmodule

// Bind into DUT
bind clock_gate clock_gate_sva u_clock_gate_sva (.*);
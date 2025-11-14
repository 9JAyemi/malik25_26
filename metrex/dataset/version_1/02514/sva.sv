// SVA for register_adder_clock_gate
// Bind this checker to the DUT
bind register_adder_clock_gate register_adder_clock_gate_chk i_register_adder_clock_gate_chk (
  .CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK), .gated_clk(gated_clk)
);

module register_adder_clock_gate_chk (
  input CLK, EN, TE, ENCLK, gated_clk
);

  // Sample on both edges so we can reason about half-cycles
  default clocking cb @(posedge CLK or negedge CLK); endclocking

  let rose_clk = $rose(CLK);
  let fell_clk = $fell(CLK);

  // 1) Output is exactly the AND of CLK and the registered enable
  assert property (ENCLK == (gated_clk & CLK))
    else $error("ENCLK must equal gated_clk & CLK");

  // 2) Registered enable updates to EN && !TE at each rising edge (guard first cycle)
  assert property (@(posedge CLK) disable iff(!$past(1'b1))
                   gated_clk == $past(EN && !TE))
    else $error("gated_clk incorrectly latched");

  // 3) No high when CLK is low
  assert property (!CLK |-> !ENCLK)
    else $error("ENCLK high while CLK low");

  // 4) ENCLK can only change when CLK changes (no glitches)
  assert property ( ($rose(ENCLK) || $fell(ENCLK)) |-> (rose_clk || fell_clk) )
    else $error("ENCLK changed without a CLK edge");

  // 5) Each rising edge of ENCLK occurs iff enable condition is true at that posedge
  assert property (@(posedge CLK) ($rose(ENCLK) == (EN && !TE)))
    else $error("ENCLK rise does not match EN && !TE at posedge");

  // 6) Basic X-checks after first cycle
  assert property (disable iff(!$past(1'b1)) !$isunknown({EN,TE,gated_clk,ENCLK}))
    else $error("X/Z detected on inputs/outputs");

  // Coverage
  cover property (@(posedge CLK) $rose(ENCLK));          // See a gated clock pulse
  cover property (@(posedge CLK) (EN && !TE));           // Enable sampled high
  cover property (@(posedge CLK) (EN && !TE) ##1 (!EN || TE)); // Enable then disable sequence

endmodule
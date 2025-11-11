// SVA for my_clock_gate
// Bind-friendly checker that references the DUT’s internal EN_reg

module my_clock_gate_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic ENCLK,
  input logic EN_reg   // bind to DUT.EN_reg
);

  // Structural relation must always hold
  assert property (@(posedge CLK or negedge CLK or posedge TE)
                   ENCLK == (EN_reg & CLK));

  // Output low whenever CLK is low
  assert property (@(negedge CLK) !ENCLK);

  // ENCLK can only rise on CLK rising edge with enable set and TE deasserted
  assert property (@(posedge ENCLK) $rose(CLK) && EN && !TE);

  // ENCLK only changes when CLK changes or TE rises (no glitches)
  assert property (@(posedge ENCLK or negedge ENCLK) $changed(CLK) || $rose(TE));

  // EN_reg captures EN on posedge CLK when TE==0; else forced 0
  assert property (@(posedge CLK) EN_reg == ($past(TE) ? 1'b0 : $past(EN)));

  // While TE is high, state/output must be 0
  assert property (@(posedge CLK) TE |-> (EN_reg==1'b0 && ENCLK==1'b0));

  // No X on output when inputs are known
  assert property (@(posedge CLK or negedge CLK or posedge TE)
                   !$isunknown({CLK,EN,TE}) |-> !$isunknown(ENCLK));

  // Coverage: enabled pulse observed
  cover property (@(posedge ENCLK) EN && !TE);

  // Coverage: pulse terminates (fall seen after rise)
  cover property (@(posedge ENCLK) ##[1:$] $fell(ENCLK));

  // Coverage: TE truncates a high pulse
  cover property (@(posedge ENCLK) ##[1:$] $rose(TE) ##[0:1] $fell(ENCLK));

endmodule

// Bind into the DUT (connect internal EN_reg)
bind my_clock_gate my_clock_gate_sva sva_i (
  .CLK   (CLK),
  .EN    (EN),
  .TE    (TE),
  .ENCLK (ENCLK),
  .EN_reg(EN_reg)
);
// SVA checker for hard_sync
module hard_sync_sva #(
  parameter bit INIT = 1'b0,
  parameter bit IS_CLK_INVERTED = 1'b0,
  parameter int LATENCY = 2
)(
  input  logic       CLK,
  input  logic       DIN,
  input  logic       DOUT,
  input  logic [2:0] DIN_reg
);

  // Parameter legality
  initial begin
    assert (LATENCY == 2 || LATENCY == 3)
      else $error("hard_sync: LATENCY must be 2 or 3, got %0d", LATENCY);
    assert (DIN_reg === {3{INIT}})
      else $error("hard_sync: DIN_reg did not init to {INIT,INIT,INIT}");
  end

  // Helper: effective sampled input (dependent on IS_CLK_INVERTED)
  wire eff_din = IS_CLK_INVERTED ? ~DIN : DIN;

  // History-ready after LATENCY clocks
  int unsigned seen;
  always @(posedge CLK) begin
    if (seen < LATENCY) seen <= seen + 1;
  end
  wire hist_ok = (seen >= LATENCY);

  // Core functional check: DOUT equals eff_din delayed by LATENCY cycles
  assert property (@(posedge CLK) hist_ok |-> DOUT == $past(eff_din, LATENCY))
    else $error("hard_sync: DOUT mismatch vs eff_din delayed by LATENCY");

  // Internal shift register behavior
  // On the next clock, DIN_reg should equal previous {DIN_reg[1:0], eff_din}
  assert property (@(posedge CLK) 1'b1 |=> DIN_reg == { $past(DIN_reg[1:0]), $past(eff_din) })
    else $error("hard_sync: DIN_reg shift behavior incorrect");

  // Output muxing from DIN_reg according to LATENCY branch
  assert property (@(posedge CLK) (LATENCY==2) |-> DOUT == $past(DIN_reg[1]))
    else $error("hard_sync: DOUT should source DIN_reg[1] when LATENCY==2");
  assert property (@(posedge CLK) (LATENCY==3) |-> DOUT == $past(DIN_reg[2]))
    else $error("hard_sync: DOUT should source DIN_reg[2] when LATENCY==3");

  // No X/Z on outputs once history is valid
  assert property (@(posedge CLK) hist_ok |-> !$isunknown(DOUT) && !$isunknown(DIN_reg))
    else $error("hard_sync: X/Z detected on outputs after pipeline warm-up");

  // Coverage: rising/falling eff_din propagates to DOUT after LATENCY
  cover property (@(posedge CLK) hist_ok && $rose(eff_din) ##LATENCY $rose(DOUT));
  cover property (@(posedge CLK) hist_ok && $fell(eff_din) ##LATENCY $fell(DOUT));

endmodule

// Bind to DUT (connect internal DIN_reg explicitly)
bind hard_sync hard_sync_sva #(
  .INIT(INIT),
  .IS_CLK_INVERTED(IS_CLK_INVERTED),
  .LATENCY(LATENCY)
) hard_sync_sva_i (
  .CLK(CLK),
  .DIN(DIN),
  .DOUT(DOUT),
  .DIN_reg(DIN_reg)
)
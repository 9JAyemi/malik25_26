// SVA for antiDroopIIR_16
// Bind into the DUT; focuses on pipeline integrity, accumulator behavior,
// overflow/saturation, and output behavior. Concise but full coverage.

bind antiDroopIIR_16 antiDroopIIR_16_sva();
module antiDroopIIR_16_sva;

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  // 1) Pipeline integrity (2-flop syncs and data staging)
  assert property (past_valid |-> tapWeight_a == $past(tapWeight));
  assert property (past_valid |-> tapWeight_b == $past(tapWeight_a));
  assert property (past_valid |-> trig_a      == $past(trig));
  assert property (past_valid |-> trig_b      == $past(trig_a));
  assert property (past_valid |-> din_del     == $past(din));
`ifdef ADDPIPEREG
  assert property (past_valid |-> din_del_b   == $past(din_del));
`endif

  // 2) Multiplier result timing
`ifdef ADDPIPEREG
  // multreg <= din_del * tapWeight_b;
  assert property (past_valid |-> ##1 multreg == $past(din_del) * $past(tapWeight_b));
`else
  // multreg <= din * tapWeight_b;
  assert property (past_valid |-> ##1 multreg == $past(din) * $past(tapWeight_b));
`endif

  // 3) Accumulator update and clear
  // Clear takes priority when trig_edge && accClr_en is true that cycle.
  assert property (past_valid && $past(trig_edge && accClr_en)  |-> tap == 48'sd0);
  assert property (past_valid && !$past(trig_edge && accClr_en) |-> tap == $past(multreg) + $past(tap));

  // 4) Overflow detect correctness and registration
  assert property (oflow == ((~&tap[47:IIR_scale+15]) && (~&(~tap[47:IIR_scale+15]))));
  assert property (past_valid |-> oflowDetect == $past(oflow));

  // 5) Output behavior (saturate vs. add path)
`ifdef ADDPIPEREG
  // Saturation path
  assert property (past_valid && $past(oflow)
                   |-> dout == ($past(tap[IIR_scale+16]) ? -16'sd32768 : 16'sd32767));
  // Non-saturation path
  assert property (past_valid && !$past(oflow)
                   |-> dout == $past(din_del_b) + $past(tap[IIR_scale+15:IIR_scale]));
`else
  // Saturation path
  assert property (past_valid && $past(oflow)
                   |-> dout == ($past(tap[IIR_scale+16]) ? -16'sd32768 : 16'sd32767));
  // Non-saturation path
  assert property (past_valid && !$past(oflow)
                   |-> dout == $past(din_del) + $past(tap[IIR_scale+15:IIR_scale]));
`endif

  // 6) Trig edge well-formed (one-cycle pulse on rising edge through the 2-flop sync)
  assert property (trig_edge |-> (trig_a && !$past(trig_a)));

  // 7) Basic X-checks on outputs (after first cycle)
  assert property (past_valid |-> !$isunknown({dout, oflowDetect}));

  // 8) Coverage: clear, both saturation polarities, and normal add path
  cover property (past_valid && trig_edge && accClr_en);
  cover property (past_valid && $past(oflow) &&  $past(tap[IIR_scale+16]));  // neg sat
  cover property (past_valid && $past(oflow) && !$past(tap[IIR_scale+16]));  // pos sat
  cover property (past_valid && !$past(oflow));                              // add path

endmodule
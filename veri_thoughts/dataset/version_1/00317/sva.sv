// SVA checkers for TLATNTSCAX2TS and its wrapper
// Focus: concise, high-quality functional and safety checks + essential coverage

// Checker for leaf TLATNTSCAX2TS
module tlatntscax2ts_sva (input E, SE, CK, ECK);

  bit past_valid;
  initial past_valid = 0;
  always @(posedge CK) past_valid <= 1'b1;

  // No-X at sampling
  assert property (@(posedge CK) !$isunknown({SE,E}))
    else $error("TLATNTSCAX2TS: X/Z on control/data at posedge CK");

  // Hold when SE=0: output must retain previous value
  assert property (@(posedge CK) disable iff (!past_valid || $isunknown({SE,E,ECK}))
                   !SE |=> (ECK == $past(ECK)))
    else $error("TLATNTSCAX2TS: ECK changed while SE=0");

  // Update when SE=1: next-cycle ECK equals sampled E
  assert property (@(posedge CK) disable iff (!past_valid || $isunknown({SE,E}))
                   SE |=> (ECK == $past(E)))
    else $error("TLATNTSCAX2TS: ECK did not update to prior E when SE=1");

  // Any inter-cycle change of ECK must be due to prior SE=1
  assert property (@(posedge CK) disable iff (!past_valid || $isunknown({SE,ECK}))
                   (ECK != $past(ECK)) |-> $past(SE))
    else $error("TLATNTSCAX2TS: ECK changed without SE=1 on previous posedge");

  // Coverage: capture both update polarities and hold behavior
  cover property (@(posedge CK) past_valid && SE &&  E |=> (ECK == 1'b1));
  cover property (@(posedge CK) past_valid && SE && !E |=> (ECK == 1'b0));
  cover property (@(posedge CK) past_valid && !SE |=> (ECK == $past(ECK)));

endmodule

bind TLATNTSCAX2TS tlatntscax2ts_sva tlatntscax2ts_sva_i (.*);

// Checker for wrapper SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_1_1
module icg_sva (input CLK, EN, TE, ENCLK);

  bit past_valid;
  initial past_valid = 0;
  always @(posedge CLK) past_valid <= 1'b1;

  // No-X at sampling
  assert property (@(posedge CLK) !$isunknown({TE,EN}))
    else $error("ICG wrapper: X/Z on control/data at posedge CLK");

  // Hold when TE=0
  assert property (@(posedge CLK) disable iff (!past_valid || $isunknown({TE,ENCLK}))
                   !TE |=> (ENCLK == $past(ENCLK)))
    else $error("ICG wrapper: ENCLK changed while TE=0");

  // Update when TE=1: ENCLK follows EN with one-cycle latency
  assert property (@(posedge CLK) disable iff (!past_valid || $isunknown({TE,EN}))
                   TE |=> (ENCLK == $past(EN)))
    else $error("ICG wrapper: ENCLK did not update to prior EN when TE=1");

  // Any change on ENCLK across cycles implies prior TE=1
  assert property (@(posedge CLK) disable iff (!past_valid || $isunknown({TE,ENCLK}))
                   (ENCLK != $past(ENCLK)) |-> $past(TE))
    else $error("ICG wrapper: ENCLK changed without TE=1 on previous posedge");

  // Coverage
  cover property (@(posedge CLK) past_valid && TE &&  EN |=> (ENCLK == 1'b1));
  cover property (@(posedge CLK) past_valid && TE && !EN |=> (ENCLK == 1'b0));
  cover property (@(posedge CLK) past_valid && !TE |=> (ENCLK == $past(ENCLK)));

endmodule

bind SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_1_1 icg_sva icg_sva_i (.*);
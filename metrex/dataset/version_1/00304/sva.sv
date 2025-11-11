// SVA for TLATNTSCAX2TS and clock_gate
// Focus: functional equivalence, independence from CK/CLK, change causality, and compact coverage.

module TLATNTSCAX2TS_sva (
  input E, SE, CK, ECK
);
  // Evaluate on any relevant edge to catch combinational mismatches promptly
  localparam dummy = 0;
  // Functional equivalence when inputs are known
  a_func: assert property (@(posedge E or negedge E or posedge SE or negedge SE or posedge ECK or negedge ECK)
                           !$isunknown({E,SE}) |-> (ECK == (E & SE)));

  // Output cannot be X/Z when inputs are known
  a_no_x_out: assert property (@(posedge E or negedge E or posedge SE or negedge SE)
                               !$isunknown({E,SE}) |-> !$isunknown(ECK));

  // Output changes only if an input changes
  a_dep: assert property (@(posedge E or negedge E or posedge SE or negedge SE or posedge ECK or negedge ECK)
                          $changed(ECK) |-> ($changed(E) || $changed(SE)));

  // CK has no effect if E and SE are stable
  a_ck_indep: assert property (@(posedge CK or negedge CK)
                               $stable({E,SE}) |-> $stable(ECK));

  // Coverage: all input combinations seen with matching output
  c_00: cover property (@(posedge E or negedge E or posedge SE or negedge SE) !E && !SE && (ECK==0));
  c_01: cover property (@(posedge E or negedge E or posedge SE or negedge SE) !E &&  SE && (ECK==0));
  c_10: cover property (@(posedge E or negedge E or posedge SE or negedge SE)  E && !SE && (ECK==0));
  c_11: cover property (@(posedge E or negedge E or posedge SE or negedge SE)  E &&  SE && (ECK==1));

  // Coverage: each input toggle propagates when the other is 1
  c_toggle_E:  cover property (@(posedge E or negedge E)  SE && $changed(E)  && $changed(ECK));
  c_toggle_SE: cover property (@(posedge SE or negedge SE) E  && $changed(SE) && $changed(ECK));
endmodule

bind TLATNTSCAX2TS TLATNTSCAX2TS_sva tlatntscax2ts_sva_bind (.*);


module clock_gate_sva (
  input CLK, EN, TE, ENCLK
);
  // Functional equivalence when inputs are known
  a_func: assert property (@(posedge EN or negedge EN or posedge TE or negedge TE or posedge ENCLK or negedge ENCLK)
                           !$isunknown({EN,TE}) |-> (ENCLK == (EN & TE)));

  // Output cannot be X/Z when inputs are known
  a_no_x_out: assert property (@(posedge EN or negedge EN or posedge TE or negedge TE)
                               !$isunknown({EN,TE}) |-> !$isunknown(ENCLK));

  // Output changes only if an input changes
  a_dep: assert property (@(posedge EN or negedge EN or posedge TE or negedge TE or posedge ENCLK or negedge ENCLK)
                          $changed(ENCLK) |-> ($changed(EN) || $changed(TE)));

  // CLK has no effect if EN and TE are stable
  a_clk_indep: assert property (@(posedge CLK or negedge CLK)
                                $stable({EN,TE}) |-> $stable(ENCLK));

  // Coverage: all input combinations seen with matching output
  c_00: cover property (@(posedge EN or negedge EN or posedge TE or negedge TE) !EN && !TE && (ENCLK==0));
  c_01: cover property (@(posedge EN or negedge EN or posedge TE or negedge TE) !EN &&  TE && (ENCLK==0));
  c_10: cover property (@(posedge EN or negedge EN or posedge TE or negedge TE)  EN && !TE && (ENCLK==0));
  c_11: cover property (@(posedge EN or negedge EN or posedge TE or negedge TE)  EN &&  TE && (ENCLK==1));

  // Coverage: each input toggle propagates when the other is 1
  c_toggle_EN: cover property (@(posedge EN or negedge EN) TE && $changed(EN) && $changed(ENCLK));
  c_toggle_TE: cover property (@(posedge TE or negedge TE) EN && $changed(TE) && $changed(ENCLK));
endmodule

bind clock_gate clock_gate_sva clock_gate_sva_bind (.*);
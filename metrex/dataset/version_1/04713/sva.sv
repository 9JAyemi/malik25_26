// SVA for clock_gate: checks synchronous behavior and provides compact coverage

module clock_gate_sva (input logic CLK, EN, TE, ENCLK);
  // Make $past safe from time 0
  logic past_valid;
  always @(posedge CLK) past_valid <= 1'b1;

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!past_valid);

  // ENCLK must equal the sampled (EN && TE) from the same clock edge
  a_enclk_func: assert property (ENCLK === $past(EN && TE))
    else $error("ENCLK != sampled (EN && TE)");

  // If ENCLK is high now, both EN and TE had to be high at the sampling edge
  a_high_only_if_both_high: assert property (ENCLK |-> $past(EN && TE))
    else $error("ENCLK high without both EN and TE high at sample");

  // When inputs were known at the sampling edge, output must be known now
  a_no_x_out_when_inputs_known: assert property (!$isunknown($past({EN,TE})) |-> !$isunknown(ENCLK))
    else $error("ENCLK unknown despite known inputs");

  // Functional coverage: all input combinations at sample and resulting ENCLK
  c_combo_00: cover property (!$past(EN) && !$past(TE) && ENCLK==0);
  c_combo_01: cover property (!$past(EN) &&  $past(TE) && ENCLK==0);
  c_combo_10: cover property ( $past(EN) && !$past(TE) && ENCLK==0);
  c_combo_11: cover property ( $past(EN) &&  $past(TE) && ENCLK==1);

  // Coverage: ENCLK edges (rise/fall)
  c_enclk_rise: cover property ($past(ENCLK)==0 && ENCLK==1);
  c_enclk_fall: cover property ($past(ENCLK)==1 && ENCLK==0);
endmodule

bind clock_gate clock_gate_sva u_clock_gate_sva(.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK));
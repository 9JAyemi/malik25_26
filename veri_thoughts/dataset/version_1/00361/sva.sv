// SVA for DFFE and d_ff_en_gate
// Focused, high-quality checks with essential coverage

// Assertions for the generic DFFE
module DFFE_sva (input logic CLK, D, EN, Q);
  logic past_valid;
  always @(posedge CLK) past_valid <= 1'b1;

  // Functional correctness: capture when EN=1, hold when EN=0
  assert property (@(posedge CLK) disable iff (!past_valid)
                   $past(EN) |-> (Q == $past(D)));
  assert property (@(posedge CLK) disable iff (!past_valid)
                   !$past(EN) |-> (Q == $past(Q)));

  // Change on Q only allowed when EN was asserted on prior CLK edge
  assert property (@(posedge CLK) disable iff (!past_valid)
                   (Q != $past(Q)) |-> $past(EN));

  // Coverage
  cover property (@(posedge CLK) past_valid && $past(EN)  && (Q == $past(D)));
  cover property (@(posedge CLK) past_valid && !$past(EN) && (Q == $past(Q)));
endmodule

// Assertions for d_ff_en_gate
module d_ff_en_gate_sva (input logic CLK, D, EN, TE, Q, ENCLK);
  // Track posedge domains
  logic pv_clk, pv_enclk;
  always @(posedge CLK)    pv_clk    <= 1'b1;
  always @(posedge ENCLK)  pv_enclk  <= 1'b1;

  // Gated clock flop behavior (DFFE with D=EN, EN=TE) observed one-CLK later
  assert property (@(posedge CLK) disable iff (!pv_clk)
                   $past(TE) |-> (ENCLK == $past(EN)));
  assert property (@(posedge CLK) disable iff (!pv_clk)
                   !$past(TE) |-> (ENCLK == $past(ENCLK)));

  // ENCLK edges must come from TE=1 and EN deciding direction (checked via 1-cycle-late view)
  assert property (@(posedge CLK) disable iff (!pv_clk)
                   $rose(ENCLK) |-> ($past(TE) && $past(EN)));
  assert property (@(posedge CLK) disable iff (!pv_clk)
                   $fell(ENCLK) |-> ($past(TE) && !$past(EN)));

  // Data flop on gated clock: capture/hold semantics per EN at prior ENCLK edge
  assert property (@(posedge ENCLK) disable iff (!pv_enclk)
                   $past(EN) |-> (Q == $past(D)));
  assert property (@(posedge ENCLK) disable iff (!pv_enclk)
                   !$past(EN) |-> (Q == $past(Q)));

  // Q may only change across ENCLK edges when EN was asserted at the prior edge
  assert property (@(posedge ENCLK) disable iff (!pv_enclk)
                   (Q != $past(Q)) |-> $past(EN));

  // Coverage: gated clock rises/falls and Q updates/holds
  cover property (@(posedge CLK)    pv_clk   && $rose(ENCLK));
  cover property (@(posedge CLK)    pv_clk   && $fell(ENCLK));
  cover property (@(posedge ENCLK)  pv_enclk && $past(EN)  && (Q == $past(D)));
  cover property (@(posedge ENCLK)  pv_enclk && !$past(EN) && (Q == $past(Q)));
endmodule

// Bind the SVA to the DUTs
bind DFFE        DFFE_sva          dffe_sva_i   (.CLK(CLK), .D(D), .EN(EN), .Q(Q));
bind d_ff_en_gate d_ff_en_gate_sva dffgate_sva_i(.CLK(CLK), .D(D), .EN(EN), .TE(TE), .Q(Q), .ENCLK(ENCLK));
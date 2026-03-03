// SVA for clock_gate: concise, high-quality checks and coverage
module cg_sva (input CLK, EN, TE, ENCLK, input gated_clk);

  // Track when at least one posedge has occurred (for $past validity)
  logic posedge_seen;
  initial posedge_seen = 1'b0;
  always @(posedge CLK) posedge_seen <= 1'b1;

  // X checks
  a_no_x:          assert property (@(posedge CLK or negedge CLK) !$isunknown({CLK,EN,TE,ENCLK}));

  // Internal structure/updates
  a_and_eq:        assert property (@(posedge CLK or negedge CLK) ENCLK == (gated_clk & CLK));
  a_gc_edgeonly:   assert property (@(posedge CLK or negedge CLK) $changed(gated_clk) |-> $rose(CLK));
  a_gc_func:       assert property (disable iff (!posedge_seen)
                                   @(posedge CLK) gated_clk == $past(EN && !TE));

  // Functional behavior at output
  a_lowphase_0:    assert property (@(posedge CLK or negedge CLK) !CLK |-> (ENCLK==1'b0));
  a_enclk_model:   assert property (disable iff (!posedge_seen)
                                   @(posedge CLK or negedge CLK)
                                   ENCLK == (CLK & $past(EN && !TE, 1, posedge CLK)));

  // No glitches: ENCLK changes only when CLK changes
  a_enclk_edgeonly:assert property (@(posedge CLK or negedge CLK) $changed(ENCLK) |-> $changed(CLK));

  // Edge-cause checks
  a_enclk_rise:    assert property (disable iff (!posedge_seen)
                                   @(posedge CLK or negedge CLK)
                                   $rose(ENCLK) |-> ($rose(CLK) && $past(EN && !TE,1,posedge CLK)));
  a_enclk_fall:    assert property (@(posedge CLK or negedge CLK)
                                   $fell(ENCLK) |-> ($rose(CLK) || $fell(CLK)));

  // Coverage
  c_en_enable:     cover  property (@(posedge CLK) EN && !TE);
  c_te_override:   cover  property (@(posedge CLK) EN &&  TE);
  c_enclk_rise:    cover  property (@(posedge CLK or negedge CLK) $rose(ENCLK));
  c_enclk_fall:    cover  property (@(posedge CLK or negedge CLK) $fell(ENCLK));
  c_en_toggle:     cover  property (@(posedge CLK) $changed(EN));
  c_te_toggle:     cover  property (@(posedge CLK) $changed(TE));

endmodule

bind clock_gate cg_sva u_cg_sva (.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK), .gated_clk(gated_clk));
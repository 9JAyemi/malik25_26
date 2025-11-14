// SVA for SNPS_CLOCK_GATE_HIGH_RegisterAdd_W55_0_2
module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W55_0_2_sva (input CLK, EN, TE, ENCLK);

  // Basic functional correctness (intended ICG behavior)
  // - When TE==1: ENCLK must equal CLK
  // - When TE==0 and EN==1: ENCLK must equal CLK
  // - When TE==0 and EN==0: ENCLK must be 0
  assert property (@(posedge CLK or negedge CLK or posedge EN or negedge EN or posedge TE or negedge TE)
                   ((TE || EN) -> (ENCLK == CLK)) and ((!TE && !EN) -> (ENCLK == 1'b0)))
    else $error("ENCLK functional mismatch vs. CLK/EN/TE");

  // No X/Z on observable output
  assert property (@(posedge CLK or negedge CLK or posedge EN or negedge EN or posedge TE or negedge TE)
                   !$isunknown({EN,TE,ENCLK}))
    else $error("X/Z detected on EN/TE/ENCLK");

  // Glitch-free: ENCLK edges only occur on CLK edges
  assert property (@(posedge ENCLK) $rose(CLK))
    else $error("ENCLK rose without CLK rising");
  assert property (@(negedge ENCLK) $fell(CLK))
    else $error("ENCLK fell without CLK falling");

  // When disabled (TE==0 && EN==0), ENCLK must remain low at CLK edges
  assert property (@(posedge CLK or negedge CLK) (!TE && !EN) |-> (ENCLK==1'b0))
    else $error("ENCLK not low while gated off");

  // When enabled (TE||EN), ENCLK must track CLK at its edges
  assert property (@(posedge CLK) (TE || EN) |-> (ENCLK==1'b1))
    else $error("ENCLK did not rise with CLK while enabled");
  assert property (@(negedge CLK) (TE || EN) |-> (ENCLK==1'b0))
    else $error("ENCLK did not fall with CLK while enabled");

  // Coverage: exercise key modes and corner cases
  cover property (@(posedge CLK) (!TE && !EN) ##1 (!TE && !EN) ##1 (ENCLK==0));                         // gated off holds low
  cover property (@(posedge ENCLK) (!TE && EN));                                                        // normal enable causes ENCLK rise
  cover property (@(negedge ENCLK) (!TE && EN));                                                        // normal enable causes ENCLK fall
  cover property (@(posedge ENCLK) TE);                                                                 // test enable causes ENCLK rise
  cover property (@(posedge EN) CLK);                                                                   // enable asserted while CLK high
  cover property (@(negedge EN) CLK);                                                                   // enable deasserted while CLK high
  cover property (@(posedge TE) (!EN && CLK));                                                          // TE asserted while EN=0 and CLK high

endmodule

// Bind into DUT
bind SNPS_CLOCK_GATE_HIGH_RegisterAdd_W55_0_2 SNPS_CLOCK_GATE_HIGH_RegisterAdd_W55_0_2_sva u_sva (.*);
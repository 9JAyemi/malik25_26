// SVA for clock_gate modules

module clock_gate_sva (input logic CLK, EN, TE, ENCLK);

  // Functional equivalence and knownness (checks on any relevant edge)
  assert property (@(posedge CLK or negedge CLK or
                     posedge EN  or negedge EN  or
                     posedge TE  or negedge TE  or
                     posedge ENCLK or negedge ENCLK)
                   !$isunknown({CLK,EN,TE}) |-> (ENCLK === ((~EN) | (EN & TE & CLK)) && !$isunknown(ENCLK)))
    else $error("clock_gate: ENCLK != (~EN)|(EN&TE&CLK) or X detected");

  // Pass-through: when EN&&TE stable, CLK edges propagate to ENCLK
  assert property (@(posedge CLK or negedge CLK)
                   EN && TE && $stable(EN) && $stable(TE) && $changed(CLK)
                   |-> $changed(ENCLK) && (ENCLK == CLK));

  // Gated hold: output stable vs CLK edges when disabled modes
  assert property (@(posedge CLK or negedge CLK)
                   !EN && $stable(EN) && $changed(CLK) |-> $stable(ENCLK) && ENCLK);

  assert property (@(posedge CLK or negedge CLK)
                   EN && !TE && $stable(EN) && $stable(TE) && $changed(CLK)
                   |-> $stable(ENCLK) && !ENCLK);

  // Minimal functional coverage
  cover property (@(posedge CLK) !EN);
  cover property (@(posedge CLK) EN && !TE);
  cover property (@(posedge CLK) EN && TE && $rose(CLK));
  cover property (@(negedge CLK) EN && TE && $fell(CLK));
  cover property (@(posedge CLK) $rose(EN) && TE);   // enter pass-through via EN
  cover property (@(posedge CLK) EN && $rose(TE));   // enter pass-through via TE
  cover property (@(posedge CLK) $fell(EN));         // exit to high-hold
  cover property (@(posedge CLK) EN && $fell(TE));   // exit to low-hold

endmodule

// Bind to both DUTs
bind clock_gate_1 clock_gate_sva cg1_sva (.*);
bind clock_gate_2 clock_gate_sva cg2_sva (.*);
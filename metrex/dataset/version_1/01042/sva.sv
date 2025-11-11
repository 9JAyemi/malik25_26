// SVA for clock gating wrapper and cell
// Focus: functional equivalence, edge alignment, glitch-free usage, and coverage.

module clock_gate_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic ENCLK
);

  // 1) Functional equivalence (sample on relevant events)
  assert property (@(posedge CLK or negedge CLK or posedge EN or negedge EN or posedge TE or negedge TE)
                   ENCLK === (CLK & (EN | ~TE)))
    else $error("ENCLK != CLK & (EN | ~TE)");

  // 2) Output must be 0 when CLK is 0
  assert property (@(negedge CLK) ENCLK == 1'b0)
    else $error("ENCLK not low on CLK low");

  // 3) Edge alignment and enable behavior
  assert property (@(posedge CLK) ENCLK == (EN | ~TE))
    else $error("ENCLK posedge mismatch with gating condition");
  assert property (@(posedge CLK or negedge CLK) (!TE) |-> (ENCLK == CLK))
    else $error("TE=0 bypass should pass CLK through");
  assert property (@(posedge CLK) (TE && !EN) |-> (ENCLK == 1'b0))
    else $error("TE=1, EN=0 must block clock");
  assert property (@(posedge CLK) (TE && EN) |-> (ENCLK == 1'b1))
    else $error("TE=1, EN=1 must pass posedge");

  // 4) No glitches: ENCLK may change only with CLK edges
  assert property (@(posedge ENCLK) $rose(CLK))
    else $error("ENCLK rose without CLK rising");
  assert property (@(negedge ENCLK) $fell(CLK))
    else $error("ENCLK fell without CLK falling");

  // 5) Safe-usage constraint for glitch-free gating:
  // Control signals must not change while CLK is high
  assert property (@(posedge EN or negedge EN) !CLK)
    else $error("EN changed while CLK high (glitch risk)");
  assert property (@(posedge TE or negedge TE) !CLK)
    else $error("TE changed while CLK high (glitch risk)");

  // 6) Knownness: if inputs are known, output must be known
  assert property (@(posedge CLK or negedge CLK)
                   !$isunknown({CLK,EN,TE}) |-> !$isunknown(ENCLK))
    else $error("ENCLK unknown with known inputs");

  // 7) Coverage
  cover property (@(posedge CLK) !TE);                  // bypass mode (TE=0)
  cover property (@(posedge CLK) TE && EN);             // gated on via EN
  cover property (@(posedge CLK) TE && !EN);            // gated off
  cover property (@(posedge ENCLK) 1);                  // observed a gated posedge
  cover property (@(negedge ENCLK) 1);                  // observed a gated negedge
  cover property (@(posedge EN or negedge EN) !CLK);    // control change during CLK low
  cover property (@(posedge TE or negedge TE) !CLK);

endmodule

// Bind to both the wrapper and the cell (optional: keeps checks consistent)
bind clock_gate_d_ff_en_W32_0_11 clock_gate_sva (.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK));
bind TLALATCH                     clock_gate_sva (.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(GATED_CLK));
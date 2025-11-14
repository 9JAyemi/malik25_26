// SVA for clock_gate: concise, high-quality checks and coverage
module clock_gate_sva
  (input logic CLK, EN, TE, ENCLK);

  // Functional equivalence at any relevant edge; also ensure no X on output when inputs known
  assert property (@(posedge CLK or negedge CLK or posedge EN or negedge EN or posedge TE or negedge TE)
                   !$isunknown({CLK,EN,TE}) |-> ENCLK == (TE ? 1'b1 : (EN ? CLK : 1'b0)));
  assert property (@(posedge CLK or negedge CLK or posedge EN or negedge EN or posedge TE or negedge TE)
                   !$isunknown({CLK,EN,TE}) |-> !$isunknown(ENCLK));

  // Mode-specific behavior across clock edges
  assert property (@(posedge CLK or negedge CLK) (TE)            |-> (ENCLK == 1'b1 && $stable(ENCLK)));
  assert property (@(posedge CLK or negedge CLK) (!TE && !EN)    |-> (ENCLK == 1'b0 && $stable(ENCLK)));
  assert property (@(posedge CLK or negedge CLK) (!TE && EN)     |-> (ENCLK == CLK));

  // Immediate combinational response on control edges
  assert property (@(posedge TE)                 ##0 (ENCLK == 1'b1));
  assert property (@(negedge TE)                 ##0 (ENCLK == (EN ? CLK : 1'b0)));
  assert property (@(posedge EN)   (!TE)         |-> ##0 (ENCLK == CLK));
  assert property (@(negedge EN)   (!TE)         |-> ##0 (ENCLK == 1'b0));

  // Minimal coverage: exercise all modes and pass-through toggling
  cover property (@(posedge CLK) (TE)                          && ENCLK == 1'b1);
  cover property (@(posedge CLK) (!TE && !EN)                  && ENCLK == 1'b0);
  cover property (@(posedge CLK) (!TE && EN)                   && ENCLK == 1'b1);
  cover property (@(negedge CLK) (!TE && EN)                   && ENCLK == 1'b0);
  cover property (@(posedge TE));
  cover property (@(negedge TE));
  cover property (@(posedge EN) (!TE));
  cover property (@(negedge EN) (!TE));

endmodule

// Bind into DUT
bind clock_gate clock_gate_sva u_clock_gate_sva (.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK));
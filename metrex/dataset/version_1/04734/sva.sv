// SVA for clock_gate_register
// Bind into DUT to gain access to internal ENCLK_reg
bind clock_gate_register cg_reg_sva cg_reg_sva_inst(
  .CLK(CLK), .EN(EN), .TE(TE), .reset(reset),
  .ENCLK(ENCLK), .ENCLK_reg(ENCLK_reg)
);

module cg_reg_sva(
  input CLK, EN, TE, reset,
  input ENCLK,
  input ENCLK_reg
);
  default clocking cb @(posedge CLK); endclocking

  // Async reset forces low and holds low while reset=1
  assert property (@(posedge reset or posedge CLK)
                   reset |-> (ENCLK_reg==1'b0 && ENCLK==1'b0))
    else $error("Reset did not force ENCLK_reg/ENCLK low");

  // Combinational gating: ENCLK equals TE ? ENCLK_reg : 0
  assert property (@(posedge CLK) ENCLK == (TE ? ENCLK_reg : 1'b0))
    else $error("ENCLK gating mismatch");

  // Update on enable: when EN is 1 at posedge, ENCLK_reg becomes 1 that cycle
  assert property (@(posedge CLK) disable iff (reset)
                   EN |-> ##0 (ENCLK_reg==1'b1))
    else $error("EN high did not set ENCLK_reg to 1");

  // Hold when not enabled: ENCLK_reg stable across posedge
  assert property (@(posedge CLK) disable iff (reset)
                   !EN |-> ##0 (ENCLK_reg==$past(ENCLK_reg)))
    else $error("ENCLK_reg changed without EN");

  // Once high, stays high until reset
  assert property (@(posedge CLK) disable iff (reset)
                   ENCLK_reg |=> ENCLK_reg)
    else $error("ENCLK_reg deasserted without reset");

  // Glitch-free ENCLK_reg between clock edges (no async changes)
  assert property (@(negedge CLK) disable iff (reset) $stable(ENCLK_reg))
    else $error("ENCLK_reg changed away from posedge/reset");

  // ------------- Coverage -------------

  // Reset pulse observed
  cover property (@(posedge CLK) reset ##1 !reset);

  // EN causes ENCLK_reg to rise from 0
  cover property (@(posedge CLK) disable iff (reset)
                  (!ENCLK_reg && EN) |-> ##0 ENCLK_reg);

  // Exercise TE gating low->high and high->low while ENCLK_reg is 1
  cover property (@(posedge CLK) ENCLK_reg && !TE ##1 TE);
  cover property (@(posedge CLK) ENCLK_reg && TE ##1 !TE);
endmodule
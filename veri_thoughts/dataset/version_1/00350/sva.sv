// SVA for gated_d_ff_en
// Bind-friendly checker module. Binds to internal ENCLK_reg for stronger checks.
module gated_d_ff_en_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic ENCLK,
  input logic ENCLK_reg
);

  // 1) Output must be forced low whenever EN=0 (combinational guarantee)
  assert property ( !EN |-> (ENCLK == 1'b0) )
    else $error("EN=0 must force ENCLK=0");

  // 2) On posedge CLK with EN=1, ENCLK must update to TE immediately (NBA/##0)
  assert property (@(posedge CLK) EN |-> ##0 (ENCLK == TE))
    else $error("ENCLK must update to TE on posedge when EN=1");

  // 3) Internal state capture: ENCLK_reg captures TE on posedge when EN=1
  assert property (@(posedge CLK) EN |-> ##0 (ENCLK_reg == TE))
    else $error("ENCLK_reg must capture TE on posedge when EN=1");

  // 4) When EN=0 on posedge, ENCLK_reg must hold its value
  assert property (@(posedge CLK) !EN |-> $stable(ENCLK_reg))
    else $error("ENCLK_reg changed while EN=0");

  // 5) With EN high across consecutive clock edges, ENCLK (before update) must
  //    equal prior TE (proves hold between edges while enabled)
  assert property (@(posedge CLK) $past(EN) && EN |-> (ENCLK == $past(TE)))
    else $error("ENCLK not holding previous TE across cycle while EN=1");

  // 6) Data used when enabled must be known (sanity)
  assert property (@(posedge CLK) EN |-> !$isunknown(TE))
    else $error("TE is X/Z when sampled with EN=1");

  // Coverage: capture both 0 and 1 while enabled, and enable toggle
  cover property (@(posedge CLK) EN && !TE ##1 EN && TE); // capture 0 then 1
  cover property (@(posedge CLK) EN &&  TE ##1 EN && !TE); // capture 1 then 0
  cover property (@(posedge CLK) EN ##1 !EN);              // gate turns off

endmodule

// Bind example:
// bind gated_d_ff_en gated_d_ff_en_sva u_gated_d_ff_en_sva (.* , .ENCLK_reg(ENCLK_reg));
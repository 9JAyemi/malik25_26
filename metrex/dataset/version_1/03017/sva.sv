// SVA for sky130_fd_sc_dff and wrapper
// Focused, concise, high-value assertions and coverage

`ifndef SYNTHESIS
// -------------------- leaf DFF SVA --------------------
module sky130_fd_sc_dff_sva (
  input Q,
  input CLK_N,
  input D,
  input RESET_B,
  input VPWR, VGND, VPB, VNB
);

  // Convenience macro
  let power_ok = (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0);

  // Valid sample tracking for $past on CLK
  logic past_clk_valid;
  initial past_clk_valid = 1'b0;
  always @(posedge CLK_N or negedge RESET_B)
    if (!RESET_B) past_clk_valid <= 1'b0;
    else          past_clk_valid <= 1'b1;

  // Power rails must be valid (assumption for clean checking)
  assume property (@(posedge CLK_N or negedge RESET_B) power_ok);

  // Inputs must not be X/Z when powered
  assert property (@(posedge CLK_N or negedge RESET_B) power_ok |-> !$isunknown({CLK_N, D, RESET_B}));

  // Asynchronous reset clears immediately (next delta)
  assert property (@(negedge RESET_B) 1'b1 |=> (Q == 1'b0));

  // While reset is asserted, Q stays low
  assert property (@(posedge CLK_N or negedge RESET_B) (!RESET_B) |-> (Q == 1'b0));

  // Synchronous capture on posedge CLK_N when not in reset
  assert property (@(posedge CLK_N) disable iff (!RESET_B || !past_clk_valid)
                   Q == $past(D));

  // No X/Z on Q when powered and not in reset
  assert property (@(posedge CLK_N or negedge RESET_B) (power_ok && RESET_B) |-> !$isunknown(Q));

  // --------------- Coverage ---------------
  cover property (@(negedge RESET_B) 1);          // reset asserted
  cover property (@(posedge RESET_B) 1);          // reset deasserted
  cover property (@(posedge CLK_N) disable iff(!RESET_B) 1'b1 |=> ##0 (Q == D)); // capture happens
  cover property (@(posedge CLK_N) disable iff(!RESET_B) (D==1'b0) |=> ##0 (Q==1'b0));
  cover property (@(posedge CLK_N) disable iff(!RESET_B) (D==1'b1) |=> ##0 (Q==1'b1));

endmodule

bind sky130_fd_sc_dff sky130_fd_sc_dff_sva SVA_leaf (
  .Q(Q), .CLK_N(CLK_N), .D(D), .RESET_B(RESET_B),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);

// -------------------- wrapper SVA --------------------
module asynchronous_reset_flip_flop_sva (
  input Q,
  input CLK_N,
  input D,
  input RESET_B,
  input VPWR, VGND, VPB, VNB,
  input Q_next // internal net from DUT
);
  let power_ok = (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0);

  // Power rails assumption (same as leaf)
  assume property (@(posedge CLK_N or negedge RESET_B) power_ok);

  // Connectivity: output equals internal net at all relevant events
  assert property (@(posedge CLK_N or negedge RESET_B) Q == Q_next);

  // Pass-through behavior cover: capture observed at top level
  cover property (@(posedge CLK_N) disable iff(!RESET_B) 1'b1 |=> ##0 (Q == D));

endmodule

bind asynchronous_reset_flip_flop asynchronous_reset_flip_flop_sva SVA_wrap (
  .Q(Q), .CLK_N(CLK_N), .D(D), .RESET_B(RESET_B),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .Q_next(Q_next)
);
`endif
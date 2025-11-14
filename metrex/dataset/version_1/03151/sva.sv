// SVA for sky130_fd_sc_ms__clkdlyinv5sd2 (Y = ~A)
`ifndef SKY130_FD_SC_MS__CLKDLYINV5SD2_SVA
`define SKY130_FD_SC_MS__CLKDLYINV5SD2_SVA

`ifndef SYNTHESIS
module sky130_fd_sc_ms__clkdlyinv5sd2_sva (input logic A, Y);

  // 4-state functional equivalence and X/Z propagation
  assert property (@(*) (Y === ~A));

  // Directional edge checks (no-delay functional behavior on known edges)
  assert property (@(posedge A) (Y == 1'b0));
  assert property (@(negedge A) (Y == 1'b1));
  assert property (@(posedge Y) (A == 1'b0));
  assert property (@(negedge Y) (A == 1'b1));

  // Output must never be Z
  assert property (@(*) (Y !== 1'bz));

  // Change correlation (avoid spurious glitches when signals are known)
  assert property (@(*) (!$isunknown(A) && $changed(A)) |-> $changed(Y));
  assert property (@(*) (!$isunknown(Y) && $changed(Y)) |-> $changed(A));

  // Coverage: both stable mappings, both edge directions, and X propagation
  cover property (@(*) (A === 1'b0 && Y === 1'b1));
  cover property (@(*) (A === 1'b1 && Y === 1'b0));
  cover property (@(posedge A) $fell(Y));
  cover property (@(negedge A) $rose(Y));
  cover property (@(*) ($isunknown(A) && $isunknown(Y)));

endmodule

bind sky130_fd_sc_ms__clkdlyinv5sd2 sky130_fd_sc_ms__clkdlyinv5sd2_sva u_sva (.A(A), .Y(Y));
`endif // SYNTHESIS
`endif // guard
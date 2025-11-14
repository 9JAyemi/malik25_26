// SVA checker for sky130_fd_sc_ls__dlrtn_1
module sky130_fd_sc_ls__dlrtn_1_sva (
  input Q,
  input RESET_B,
  input D,
  input GATE_N,
  input VPWR,
  input VGND,
  input VPB,
  input VNB
);

  // Power-good definition
  wire pwr_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  // Event: any relevant input/power change
  `define EV (posedge RESET_B or negedge RESET_B or \
               posedge GATE_N  or negedge GATE_N  or \
               posedge D       or negedge D       or \
               posedge VPWR    or negedge VPWR    or \
               posedge VGND    or negedge VGND    or \
               posedge VPB     or negedge VPB     or \
               posedge VNB     or negedge VNB)

  // Knownness under good power and known inputs
  assert property (@(`EV) pwr_good && !$isunknown({RESET_B,GATE_N,D}) |-> !$isunknown(Q));

  // Truth table (RESET_B dominates)
  assert property (@(`EV) pwr_good && (RESET_B===1'b1)                        |-> (Q===1'b0));
  assert property (@(`EV) pwr_good && (RESET_B===1'b0) && (GATE_N===1'b1)     |-> (Q===D));
  assert property (@(`EV) pwr_good && (RESET_B===1'b0) && (GATE_N===1'b0)     |-> (Q===1'b1));

  // Edge-specific checks (redundant but strengthen intent and catch glitches)
  assert property (@(posedge RESET_B)                   pwr_good              |-> (Q===1'b0));
  assert property (@(posedge GATE_N)                    pwr_good && RESET_B===1'b0 |-> (Q===D));
  assert property (@(negedge GATE_N)                    pwr_good && RESET_B===1'b0 |-> (Q===1'b1));
  assert property (@(posedge D or negedge D)            pwr_good && RESET_B===1'b0 && GATE_N===1'b1 |-> (Q===D));

  // Basic power-good coverage
  cover  property (@(posedge VPWR) VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);

  // Functional coverage of key modes
  cover  property (@(`EV) pwr_good && (RESET_B===1'b1)                        && (Q===1'b0));
  cover  property (@(`EV) pwr_good && (RESET_B===1'b0) && (GATE_N===1'b0)     && (Q===1'b1));
  cover  property (@(`EV) pwr_good && (RESET_B===1'b0) && (GATE_N===1'b1) && (D===1'b0) && (Q===1'b0));
  cover  property (@(`EV) pwr_good && (RESET_B===1'b0) && (GATE_N===1'b1) && (D===1'b1) && (Q===1'b1));

  // Transition coverage
  cover  property (@(posedge RESET_B)                   pwr_good && (Q===1'b0));
  cover  property (@(posedge GATE_N)                    pwr_good && RESET_B===1'b0 && (Q===D));
  cover  property (@(negedge GATE_N)                    pwr_good && RESET_B===1'b0 && (Q===1'b1));
  cover  property (@(posedge D)                         pwr_good && RESET_B===1'b0 && GATE_N===1'b1 && (Q===D));
  cover  property (@(negedge D)                         pwr_good && RESET_B===1'b0 && GATE_N===1'b1 && (Q===D));

  `undef EV
endmodule

// Bind into the DUT
bind sky130_fd_sc_ls__dlrtn_1 sky130_fd_sc_ls__dlrtn_1_sva u_sva (.*);
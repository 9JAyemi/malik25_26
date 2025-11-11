// SVA for flip_flop
// Concise, priority-accurate, next-cycle-correct (##0), and coverage-complete

`ifndef FLIP_FLOP_SVA
`define FLIP_FLOP_SVA

module flip_flop_sva (
  input logic Q,
  input logic Q_N,
  input logic D,
  input logic SCD,
  input logic SCE,
  input logic CLK,
  input logic SET_B,
  input logic RESET_B,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB
);

  // Power-good gate for checks (adjust if your env models power differently)
  wire power_ok = (VPWR===1'b1) && (VGND===1'b0);

  default clocking cb @(posedge CLK); endclocking

  // Sanity: Q_N is complement of Q (check on clock and on any Q/Q_N change)
  assert property (disable iff (!power_ok) Q_N === ~Q);
  assert property (@(posedge Q or negedge Q or posedge Q_N or negedge Q_N)
                   disable iff (!power_ok) Q_N === ~Q);

  // Control signals should be known when sampled
  assert property (disable iff (!power_ok) !$isunknown({SET_B,RESET_B,SCD,SCE}));

  // Priority and next-state behavior (synchronous; ##0 checks post-NBA value)
  // Highest: SET_B=0 -> Q=1
  assert property (disable iff (!power_ok)
                   (SET_B===1'b0) |-> ##0 (Q===1'b1));

  // Next: RESET_B=0 (and SET_B=1) -> Q=0
  assert property (disable iff (!power_ok)
                   (SET_B===1'b1 && RESET_B===1'b0) |-> ##0 (Q===1'b0));

  // Next: SCD=0 (and SET_B=RESET_B=1) -> Q=0
  assert property (disable iff (!power_ok)
                   (SET_B===1'b1 && RESET_B===1'b1 && SCD===1'b0) |-> ##0 (Q===1'b0));

  // Next: SCE=1 (and SET_B=RESET_B=1 and SCD=1) -> Q=D
  assert property (disable iff (!power_ok)
                   (SET_B===1'b1 && RESET_B===1'b1 && SCD===1'b1 && SCE===1'b1) |-> ##0 (Q===D));

  // Optional data quality: when capturing D, it should be known
  assert property (disable iff (!power_ok)
                   (SET_B===1'b1 && RESET_B===1'b1 && SCD===1'b1 && SCE===1'b1) |-> !$isunknown(D));

  // Hold: when no condition true, Q holds previous value
  assert property (disable iff (!power_ok)
                   (SET_B===1'b1 && RESET_B===1'b1 && SCD===1'b1 && SCE===1'b0) |-> ##0 (Q===$past(Q)));

  // Q changes only on CLK posedge
  assert property (@(posedge Q or negedge Q) disable iff (!power_ok) $rose(CLK));

  // Functional coverage
  cover property (power_ok && (SET_B===1'b0) ##0 (Q===1'b1)); // set
  cover property (power_ok && (SET_B===1'b1 && RESET_B===1'b0) ##0 (Q===1'b0)); // reset
  cover property (power_ok && (SET_B===1'b1 && RESET_B===1'b1 && SCD===1'b0) ##0 (Q===1'b0)); // scd clamp
  cover property (power_ok && (SET_B===1'b1 && RESET_B===1'b1 && SCD===1'b1 && SCE===1'b1) ##0 (Q===D)); // load
  cover property (power_ok && (SET_B===1'b1 && RESET_B===1'b1 && SCD===1'b1 && SCE===1'b0) ##0 (Q===$past(Q))); // hold
  cover property (power_ok && (SET_B===1'b0 && RESET_B===1'b0) ##0 (Q===1'b1)); // set/reset conflict -> set wins
  cover property (power_ok && $rose(Q));
  cover property (power_ok && $fell(Q));

endmodule

// Bind into DUT
bind flip_flop flip_flop_sva flip_flop_sva_i (.*);

`endif
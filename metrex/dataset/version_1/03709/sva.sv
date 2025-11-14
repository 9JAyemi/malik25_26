// SVA for srlc32e
// Focused, high-signal-coverage checks and concise functional coverage.
// Bind inside DUT to access internal Q_reg.

`ifndef SRLC32E_SVA
`define SRLC32E_SVA

module srlc32e_sva;

  // Clocking and X-filter to avoid spurious failures before initialization
  default clocking cb @(posedge CLK); endclocking
  default disable iff ($isunknown({CE,A,D,Q_reg}));

  // Q_reg update/hold behavior
  ap_update: assert property (CE |-> (Q_reg == D))
    else $error("Q_reg must update to D when CE=1");
  ap_hold:   assert property (!CE |-> $stable(Q_reg))
    else $error("Q_reg must hold when CE=0");

  // Output mapping: Q is always Q_reg[A] (A selects bit 0 or 1)
  ap_q_map: assert property (1'b1 |-> (Q == (A ? Q_reg[1] : Q_reg[0])))
    else $error("Q must equal Q_reg[A]");

  // On an update, Q must reflect selected bit of D immediately
  ap_q_from_d_on_update: assert property (CE |-> (Q == (A ? D[1] : D[0])))
    else $error("Q must reflect selected D bit when CE=1");

  // Q stability when nothing affecting selection changes
  ap_q_stable_no_ce_no_a: assert property ((!CE && $stable(A)) |-> $stable(Q))
    else $error("Q should be stable when CE=0 and A stable");
  ap_q_stable_upper_only: assert property ((CE && $stable(A) && (D[1:0] == $past(Q_reg[1:0]))) |-> $stable(Q))
    else $error("Upper D bits must not affect Q");

  // Functional coverage
  cp_ce0: cover property (!CE);
  cp_ce1: cover property (CE);
  cp_a0:  cover property (!A);
  cp_a1:  cover property (A);
  cp_wr_a0: cover property (CE && !A);
  cp_wr_a1: cover property (CE &&  A);

  // A toggle should toggle Q when Q_reg[0]!=Q_reg[1] and no write occurs
  cp_a_toggle_affects_q: cover property (!CE && (Q_reg[0] != Q_reg[1]) && $changed(A) && $changed(Q));

  // Writes that change visible Q for each address value
  cp_wr_changes_q_a0: cover property (CE && !A && (D[0] != $past(Q_reg[0])) && $changed(Q));
  cp_wr_changes_q_a1: cover property (CE &&  A && (D[1] != $past(Q_reg[1])) && $changed(Q));

endmodule

bind srlc32e srlc32e_sva svainst();

`endif
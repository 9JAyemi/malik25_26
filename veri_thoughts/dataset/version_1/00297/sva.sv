// SVA checker for sky130_fd_sc_lp__iso1n (active-low sleep, clamp-to-1)
module sky130_fd_sc_lp__iso1n_sva (
  input logic X, A, SLEEP_B,
  input logic SLEEP,        // internal
  input logic VPWR, VPB,    // rails
  input logic KAGND, VNB
);

  // Power rails must be at expected constants
  always_comb
    assert (VPWR===1'b1 && VPB===1'b1 && KAGND===1'b0 && VNB===1'b0)
      else $error("iso1n: power pins not at expected constants");

  // Internal invert and functional relation
  always_comb begin
    assert (SLEEP === ~SLEEP_B) else $error("iso1n: SLEEP != ~SLEEP_B");
    assert (X === (A | ~SLEEP_B)) else $error("iso1n: X != (A | ~SLEEP_B)");
  end

  // Clamp behavior in sleep; pass-through when awake with known A
  assert property (@(posedge A or negedge A or posedge SLEEP_B or negedge SLEEP_B)
                   (SLEEP_B===1'b0) |-> (X===1'b1))
    else $error("iso1n: X not clamped high during sleep");

  assert property (@(posedge A or negedge A)
                   (SLEEP_B===1'b1 && !$isunknown(A)) |-> (X===A && !$isunknown(X)))
    else $error("iso1n: pass-through failed when awake");

  // No X on output while sleeping
  assert property (@(posedge A or negedge A or posedge SLEEP_B or negedge SLEEP_B)
                   (SLEEP_B===1'b0) |-> (!$isunknown(X) && X===1'b1))
    else $error("iso1n: X unknown during sleep");

  // Edge responsiveness
  assert property (@(negedge SLEEP_B) 1 |-> ##0 (X===1'b1))
    else $error("iso1n: X not high on entering sleep");

  assert property (@(posedge SLEEP_B) 1 |-> ##0 (X===A))
    else $error("iso1n: X not following A on exiting sleep");

  // Functional coverage
  cover property (@(negedge SLEEP_B) A===1'b0 && X===1'b1);
  cover property (@(negedge SLEEP_B) A===1'b1 && X===1'b1);
  cover property (@(posedge SLEEP_B) A===1'b0 && X===1'b0);
  cover property (@(posedge SLEEP_B) A===1'b1 && X===1'b1);
  cover property (@(posedge A)  SLEEP_B===1'b1 && X===1'b1);
  cover property (@(negedge A)  SLEEP_B===1'b1 && X===1'b0);
  cover property (@(posedge A)  SLEEP_B===1'b0 && X===1'b1);
  cover property (@(negedge A)  SLEEP_B===1'b0 && X===1'b1);

endmodule

// Bind into the DUT to access internal SLEEP and rails by name
bind sky130_fd_sc_lp__iso1n sky130_fd_sc_lp__iso1n_sva u_iso1n_sva (.*);
// SVA for sky130_fd_sc_lp__iso1n (X = A | ~SLEEP_B; clamp-high when SLEEP_B=0)
module sky130_fd_sc_lp__iso1n_sva (
  input logic A,
  input logic SLEEP_B,
  input logic X,
  input logic SLEEP // internal net
);

  // Fundamental combinational equivalence (4-state)
  always_comb begin
    assert (X === (A | ~SLEEP_B))
      else $error("iso1n func mismatch: X=%b A=%b SLEEP_B=%b", X, A, SLEEP_B);

    // Internal invert check
    assert (SLEEP === ~SLEEP_B)
      else $error("iso1n internal invert mismatch: SLEEP=%b SLEEP_B=%b", SLEEP, SLEEP_B);

    // No unknown on X when inputs are known
    if (!$isunknown({A,SLEEP_B})) assert (!$isunknown(X))
      else $error("iso1n produced X unknown with known inputs");

    // Output-low legality
    if (X === 1'b0) assert (A===1'b0 && SLEEP_B===1'b1)
      else $error("iso1n: X=0 illegal unless A=0 and SLEEP_B=1");

    // Truth-table coverage
    cover (SLEEP_B===1'b0 && X===1'b1);
    cover (SLEEP_B===1'b1 && A===1'b0 && X===1'b0);
    cover (SLEEP_B===1'b1 && A===1'b1 && X===1'b1);
    cover (SLEEP_B===1'b0 && A===1'b1 && X===1'b1);
  end

  // Mode transitions (delta-cycle tolerant)
  assert property (@(posedge SLEEP_B) ##0 X === A)
    else $error("iso1n pass-through on SLEEP_B rise failed");
  assert property (@(negedge SLEEP_B) ##0 X === 1'b1)
    else $error("iso1n clamp-1 on SLEEP_B fall failed");

  // A edges when awake: X follows A
  assert property (@(posedge A) (SLEEP_B===1'b1) |-> ##0 (X===1'b1))
    else $error("iso1n failed to rise with A when awake");
  assert property (@(negedge A) (SLEEP_B===1'b1) |-> ##0 (X===1'b0))
    else $error("iso1n failed to fall with A when awake");

  // A edges when sleeping: X must stay 1
  assert property (@(posedge A or negedge A) (SLEEP_B===1'b0) |-> ##0 (X===1'b1))
    else $error("iso1n X changed with A while sleeping");

  // Transition coverage
  cover property (@(posedge SLEEP_B) ##0 X===A);
  cover property (@(negedge SLEEP_B) ##0 X===1'b1);
  cover property (@(posedge A) (SLEEP_B===1'b1) ##0 X===1'b1);
  cover property (@(negedge A) (SLEEP_B===1'b1) ##0 X===1'b0);

endmodule

bind sky130_fd_sc_lp__iso1n sky130_fd_sc_lp__iso1n_sva u_iso1n_sva (
  .A(A),
  .SLEEP_B(SLEEP_B),
  .X(X),
  .SLEEP(SLEEP)
);
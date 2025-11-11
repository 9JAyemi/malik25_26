// SVA for sky130_fd_sc_hd__lpflow_inputiso0n
// Function: X = A & SLEEP_B (isolation active when SLEEP_B=0)

module sky130_fd_sc_hd__lpflow_inputiso0n_sva (
  input logic A,
  input logic SLEEP_B,
  input logic X
);

  // Output only changes when an input changes
  assert property (@(A or SLEEP_B or X)
    $changed(X) |-> ($changed(A) || $changed(SLEEP_B))
  ) else $error("X changed without A or SLEEP_B change");

  // When inputs are stable, output matches logical function
  assert property (@(A or SLEEP_B or X)
    ($stable(A) && $stable(SLEEP_B)) |-> (X === (A & SLEEP_B))
  ) else $error("X != A & SLEEP_B when inputs stable");

  // Isolation clamp: when SLEEP_B is stably 0, X must be 0 (and known)
  assert property (@(A or SLEEP_B or X)
    (SLEEP_B === 1'b0 && $stable(SLEEP_B)) |-> (X === 1'b0 && !$isunknown(X))
  ) else $error("Clamp failed: SLEEP_B=0 but X not 0/known");

  // Pass-through: when SLEEP_B and A are stable (and A known), X == A (and known)
  assert property (@(A or SLEEP_B or X)
    (SLEEP_B === 1'b1 && $stable(SLEEP_B) && $stable(A) && !$isunknown(A)) |-> (X === A && !$isunknown(X))
  ) else $error("Pass-through failed: SLEEP_B=1");

  // Determinism: any known 0 on an input (stable) forces X=0
  assert property (@(A or SLEEP_B or X)
    ((A === 1'b0 && $stable(A)) || (SLEEP_B === 1'b0 && $stable(SLEEP_B))) |-> (X === 1'b0)
  ) else $error("Known-0 controlling value not forcing X=0");

  // Functional coverage: all truth-table points observed
  cover property (@(A or SLEEP_B or X) (A===1'b0 && SLEEP_B===1'b0 && X===1'b0));
  cover property (@(A or SLEEP_B or X) (A===1'b0 && SLEEP_B===1'b1 && X===1'b0));
  cover property (@(A or SLEEP_B or X) (A===1'b1 && SLEEP_B===1'b0 && X===1'b0));
  cover property (@(A or SLEEP_B or X) (A===1'b1 && SLEEP_B===1'b1 && X===1'b1));

  // Coverage: isolation active, A toggles, X remains clamped low
  cover property (@(A or SLEEP_B or X)
    (SLEEP_B===1'b0) ##1 $changed(A) ##1 (X===1'b0)
  );

  // Coverage: enable isolation (SLEEP_B rises) with A=1, X goes high
  cover property (@(A or SLEEP_B or X)
    (A===1'b1 && SLEEP_B===1'b0) ##1 (SLEEP_B===1'b1) ##[0:1] (X===1'b1)
  );

  // Coverage: disable isolation (SLEEP_B falls) with A=1, X goes low
  cover property (@(A or SLEEP_B or X)
    (A===1'b1 && SLEEP_B===1'b1 && X===1'b1) ##1 (SLEEP_B===1'b0) ##[0:1] (X===1'b0)
  );

endmodule

// Bind into DUT
bind sky130_fd_sc_hd__lpflow_inputiso0n sky130_fd_sc_hd__lpflow_inputiso0n_sva u_sva (
  .A(A), .SLEEP_B(SLEEP_B), .X(X)
);
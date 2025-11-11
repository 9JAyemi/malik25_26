// SVA for sky130_fd_sc_hd__lpflow_inputiso1n
// Function: X = A | ~SLEEP_B  (clamp 1 when SLEEP_B=0, pass-through when SLEEP_B=1)

module sky130_fd_sc_hd__lpflow_inputiso1n_sva (
  input logic X,
  input logic A,
  input logic SLEEP_B,
  input logic SLEEP,   // internal net
  input logic VPWR, VGND, VPB, VNB
);

  // Power rails sanity (constant and known)
  assert property (@(A or SLEEP_B or SLEEP or X)
                   (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0))
    else $error("Power rails invalid");

  // Gate-level correctness
  assert property (@(SLEEP_B) ##0 (SLEEP === ~SLEEP_B))
    else $error("Inverter mismatch: SLEEP != ~SLEEP_B");

  assert property (@(A or SLEEP) ##0 (X === (A | SLEEP)))
    else $error("OR mismatch: X != (A | SLEEP)");

  // Functional correctness and timing (0-delay update on input changes)
  assert property (@(A or SLEEP_B)
                   (A !== 1'bx && SLEEP_B !== 1'bx) |-> ##0 (X === (A | ~SLEEP_B)))
    else $error("Functional mismatch: X != (A | ~SLEEP_B)");

  // Known-when-inputs-known
  assert property (@(A or SLEEP_B)
                   (A !== 1'bx && SLEEP_B !== 1'bx) |-> ##0 (!$isunknown(X)))
    else $error("X unknown while inputs known");

  // Mode-specific checks
  assert property (@(A or SLEEP_B) (SLEEP_B===1'b1) |-> ##0 (X===A))
    else $error("Pass-through mode failed (SLEEP_B=1)");
  assert property (@(A or SLEEP_B) (SLEEP_B===1'b0) |-> ##0 (X===1'b1))
    else $error("Clamp-1 mode failed (SLEEP_B=0)");

  // Edge-behavior checks
  assert property (@(SLEEP_B) $rose(SLEEP_B) |-> ##0 (X===A))
    else $error("On wake (SLEEP_B rise), X != A");
  assert property (@(SLEEP_B) $fell(SLEEP_B) |-> ##0 (X===1'b1))
    else $error("On sleep (SLEEP_B fall), X != 1");

  // Coverage: truth table
  cover property (@(A or SLEEP_B) (A===1'b0 && SLEEP_B===1'b0) ##0 (X===1'b1));
  cover property (@(A or SLEEP_B) (A===1'b0 && SLEEP_B===1'b1) ##0 (X===1'b0));
  cover property (@(A or SLEEP_B) (A===1'b1 && SLEEP_B===1'b0) ##0 (X===1'b1));
  cover property (@(A or SLEEP_B) (A===1'b1 && SLEEP_B===1'b1) ##0 (X===1'b1));

  // Coverage: toggles in both modes
  cover property (@(SLEEP_B) (A===1'b0 && $fell(SLEEP_B)));
  cover property (@(SLEEP_B) (A===1'b1 && $fell(SLEEP_B)));
  cover property (@(SLEEP_B) (A===1'b0 && $rose(SLEEP_B)));
  cover property (@(SLEEP_B) (A===1'b1 && $rose(SLEEP_B)));
  cover property (@(A) (SLEEP_B===1'b0 && $rose(A)));
  cover property (@(A) (SLEEP_B===1'b0 && $fell(A)));
  cover property (@(A) (SLEEP_B===1'b1 && $rose(A)));
  cover property (@(A) (SLEEP_B===1'b1 && $fell(A)));

endmodule

bind sky130_fd_sc_hd__lpflow_inputiso1n
  sky130_fd_sc_hd__lpflow_inputiso1n_sva
    sva_u (
      .X(X),
      .A(A),
      .SLEEP_B(SLEEP_B),
      .SLEEP(SLEEP),
      .VPWR(VPWR),
      .VGND(VGND),
      .VPB(VPB),
      .VNB(VNB)
    );
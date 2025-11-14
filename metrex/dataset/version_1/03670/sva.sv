// SVA for sky130_fd_sc_lp__iso1p (X = A | SLEEP)
`ifndef SKY130_FD_SC_LP__ISO1P_SVA
`define SKY130_FD_SC_LP__ISO1P_SVA

module sky130_fd_sc_lp__iso1p_sva (
  input logic X,
  input logic A,
  input logic SLEEP
);

  // Functional equivalence (sample next delta to avoid race)
  assert property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP or posedge X or negedge X)
                   1'b1 |-> ##0 (X === (A | SLEEP)))
    else $error("iso1p: X != (A|SLEEP)");

  // Clamp behavior: when SLEEP=1, X must be 1
  assert property (@(posedge SLEEP or negedge SLEEP or posedge A or negedge A)
                   SLEEP |-> ##0 (X === 1'b1))
    else $error("iso1p: SLEEP=1 must clamp X=1");

  // Pass-through when awake: when SLEEP=0, X==A
  assert property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP)
                   !SLEEP |-> ##0 (X === A))
    else $error("iso1p: SLEEP=0 must pass A to X");

  // No X/Z on output when inputs are known (4-state clean)
  assert property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP or posedge X or negedge X)
                   (!$isunknown(A) && !$isunknown(SLEEP)) |-> ##0 !$isunknown(X))
    else $error("iso1p: X unknown while inputs are known");

  // Sanity implications
  assert property (@(posedge X or negedge X) X |-> (A || SLEEP));
  assert property (@(posedge X or negedge X) !X |-> (!A && !SLEEP));

  // Coverage: full truth table
  cover property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP)
                  (!A && !SLEEP) ##0 (!X));
  cover property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP)
                  ( A && !SLEEP) ##0 ( X));
  cover property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP)
                  (!A &&  SLEEP) ##0 ( X));
  cover property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP)
                  ( A &&  SLEEP) ##0 ( X));

  // Coverage: SLEEP edges and effects
  cover property (@(posedge SLEEP) ##0 X);
  cover property (@(negedge SLEEP) ##0 (X === A));

endmodule

bind sky130_fd_sc_lp__iso1p sky130_fd_sc_lp__iso1p_sva _iso1p_sva_ (.X(X), .A(A), .SLEEP(SLEEP));

`endif
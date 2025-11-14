// SVA for sky130_fd_sc_lp__o21a: X = (A1 | A2) & B1
// Bind-module with concise checks and coverage

module sky130_fd_sc_lp__o21a_sva (
  input logic A1,
  input logic A2,
  input logic B1,
  input logic X,
  input logic or0_out,
  input logic and0_out_X
);

  // 4-state functional equivalence and structural checks
  always_comb begin
    assert #0 (X === ((A1 | A2) & B1)) else $error("X != (A1|A2)&B1");
    assert #0 (or0_out === (A1 | A2)) else $error("or0_out mismatch");
    assert #0 (and0_out_X === (or0_out & B1)) else $error("and0_out_X mismatch");
    assert #0 (X === and0_out_X) else $error("buf mismatch");

    if (!$isunknown({A1,A2,B1}))
      assert #0 (!$isunknown(X)) else $error("X unknown with known inputs");

    if (B1 === 1'b0)
      assert #0 (X === 1'b0) else $error("B1 low must force X low");
  end

  // Coverage: all input combos with expected X, plus basic toggles
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (A1===1'b0 && A2===1'b0 && B1===1'b0 && X===1'b0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (A1===1'b0 && A2===1'b0 && B1===1'b1 && X===1'b0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (A1===1'b0 && A2===1'b1 && B1===1'b0 && X===1'b0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (A1===1'b0 && A2===1'b1 && B1===1'b1 && X===1'b1));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (A1===1'b1 && A2===1'b0 && B1===1'b0 && X===1'b0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (A1===1'b1 && A2===1'b0 && B1===1'b1 && X===1'b1));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (A1===1'b1 && A2===1'b1 && B1===1'b0 && X===1'b0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  (A1===1'b1 && A2===1'b1 && B1===1'b1 && X===1'b1));

  cover property (@(posedge A1) 1);
  cover property (@(negedge A1) 1);
  cover property (@(posedge A2) 1);
  cover property (@(negedge A2) 1);
  cover property (@(posedge B1) 1);
  cover property (@(negedge B1) 1);
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

endmodule

// Bind into the DUT (place in a bind file or alongside the DUT)
bind sky130_fd_sc_lp__o21a sky130_fd_sc_lp__o21a_sva o21a_sva_i (
  .A1(A1),
  .A2(A2),
  .B1(B1),
  .X(X),
  .or0_out(or0_out),
  .and0_out_X(and0_out_X)
);
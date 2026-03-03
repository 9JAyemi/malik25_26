// SVA for sky130_fd_sc_lp__o21a: X = (A1 | A2) & B1

module o21a_sva (
  input logic A1,
  input logic A2,
  input logic B1,
  input logic X,
  // internal taps (available in this cell)
  input logic or0_out,
  input logic and0_out_X
);

  // Structural equivalence checks
  always_comb begin
    assert (or0_out    === (A1 | A2))        else $error("o21a: OR stage mismatch");
    assert (and0_out_X === (or0_out & B1))   else $error("o21a: AND stage mismatch");
    assert (X          === and0_out_X)       else $error("o21a: BUF stage mismatch");
    assert (X          === ((A1 | A2) & B1)) else $error("o21a: Functional mismatch");
  end

  // Deterministic controlling-value checks and X-masking
  always_comb begin
    if (B1 === 1'b0)                         assert (X === 1'b0) else $error("o21a: B1=0 must force X=0");
    if ((A1 === 1'b0) && (A2 === 1'b0))      assert (X === 1'b0) else $error("o21a: A1=A2=0 must force X=0");
    if ((B1 === 1'b1) && ((A1===1'b1)||(A2===1'b1)))
                                              assert (X === 1'b1) else $error("o21a: B1=1 and (A1|A2)=1 must force X=1");
  end

  // If all inputs are known, output must be known
  assert property (@(A1 or A2 or B1 or X) !$isunknown({A1,A2,B1}) |-> !$isunknown(X))
    else $error("o21a: X unknown despite known inputs");

  // Truth-table coverage (all 8 input combinations with expected X)
  always_comb begin
    cover ((A1===0)&&(A2===0)&&(B1===0)&&(X===0));
    cover ((A1===0)&&(A2===0)&&(B1===1)&&(X===0));
    cover ((A1===0)&&(A2===1)&&(B1===0)&&(X===0));
    cover ((A1===0)&&(A2===1)&&(B1===1)&&(X===1));
    cover ((A1===1)&&(A2===0)&&(B1===0)&&(X===0));
    cover ((A1===1)&&(A2===0)&&(B1===1)&&(X===1));
    cover ((A1===1)&&(A2===1)&&(B1===0)&&(X===0));
    cover ((A1===1)&&(A2===1)&&(B1===1)&&(X===1));
  end

  // Edge coverage on X
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

endmodule

bind sky130_fd_sc_lp__o21a o21a_sva o21a_sva_i (
  .A1(A1),
  .A2(A2),
  .B1(B1),
  .X(X),
  .or0_out(or0_out),
  .and0_out_X(and0_out_X)
);
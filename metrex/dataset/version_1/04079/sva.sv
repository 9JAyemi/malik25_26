// SVA for and4b: concise, high-quality checks and coverage.
// Bind this checker to the DUT type.

module and4b_sva;

  // Access DUT scope signals via bind
  // DUT ports and internals
  logic A_N, B, C, D, X, VPB, VPWR, VGND, VNB;
  logic AB, CD, ABCD;

  // Helper funcs
  function automatic bit known(input logic x);  return !$isunknown(x); endfunction
  function automatic bit known4(input logic [3:0] v); return !$isunknown(v); endfunction
  function automatic bit pg(); // power-good
    return (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);
  endfunction

  // Functional equivalence (truth table) under valid power and known inputs
  assert property (@(*) disable iff (!pg())
                    known4({A_N,B,C,D}) |-> (X === ~(A_N & B & C & D)));

  // Internal stage correctness (and stages and inverter), with X-prop sanity
  assert property (@(*) disable iff (!pg()) known4({A_N,B}) |-> (AB   === (A_N & B)));
  assert property (@(*) disable iff (!pg()) known4({C,D})   |-> (CD   === (C & D)));
  assert property (@(*) disable iff (!pg()) known(AB) && known(CD) |-> (ABCD === (AB & CD)));
  assert property (@(*) disable iff (!pg()) known(ABCD)            |-> (X    === ~ABCD));

  // Output is known when all inputs are known
  assert property (@(*) disable iff (!pg()) known4({A_N,B,C,D}) |-> known(X));

  // Controlling-0 short-circuit behavior (robust to Xs on other inputs)
  assert property (@(*) disable iff (!pg()) (A_N===1'b0) |-> (X===1'b1));
  assert property (@(*) disable iff (!pg()) (B  ===1'b0) |-> (X===1'b1));
  assert property (@(*) disable iff (!pg()) (C  ===1'b0) |-> (X===1'b1));
  assert property (@(*) disable iff (!pg()) (D  ===1'b0) |-> (X===1'b1));

  // Corner case: all ones -> only case driving X low
  assert property (@(*) disable iff (!pg())
                    (A_N===1'b1 && B===1'b1 && C===1'b1 && D===1'b1) |-> (X===1'b0));

  // Power pins not X/Z (optional but valuable sanity)
  assert property (@(*) !$isunknown({VPWR,VGND,VPB,VNB}));

  // Coverage: power good observed
  cover property (@(*) pg());

  // Coverage: only low-output minterm
  cover property (@(*) pg() && A_N && B && C && D && (X===1'b0));

  // Coverage: each single-zero input case with others high (validates each input path)
  cover property (@(*) pg() && (A_N==1'b0) &&  B &&  C &&  D && (X===1'b1));
  cover property (@(*) pg() &&  A_N        && (B==1'b0) && C &&  D && (X===1'b1));
  cover property (@(*) pg() &&  A_N        &&  B && (C==1'b0) &&  D && (X===1'b1));
  cover property (@(*) pg() &&  A_N        &&  B &&  C && (D==1'b0) && (X===1'b1));

endmodule

bind and4b and4b_sva sva_and4b();
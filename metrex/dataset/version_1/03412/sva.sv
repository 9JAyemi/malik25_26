// SVA for sky130_fd_sc_lp__o31a: X = (A1 | A2 | A3) & B1
module sky130_fd_sc_lp__o31a_sva (
  input logic A1, A2, A3, B1, X
);
  logic ora;
  assign ora = A1 | A2 | A3;

  // 4-state functional equivalence (tolerates X/Z on inputs)
  property p_equiv4; @(A1 or A2 or A3 or B1 or X) X === (B1 & ora); endproperty
  assert property (p_equiv4);

  // When inputs are known, output must be known and 2-state correct
  property p_equiv2_known;
    @(A1 or A2 or A3 or B1 or X) (! $isunknown({A1,A2,A3,B1})) |-> (! $isunknown(X) && X == (B1 & ora));
  endproperty
  assert property (p_equiv2_known);

  // Key implications
  property p_gate_b0;   @(A1 or A2 or A3 or B1 or X) (B1===1'b0) |-> (X===1'b0); endproperty
  assert property (p_gate_b0);

  property p_anyA1_eq_B1; @(A1 or A2 or A3 or B1 or X) ((A1===1) || (A2===1) || (A3===1)) |-> (X===B1); endproperty
  assert property (p_anyA1_eq_B1);

  property p_allA0_zero; @(A1 or A2 or A3 or B1 or X) (A1===0 && A2===0 && A3===0) |-> (X===1'b0); endproperty
  assert property (p_allA0_zero);

  // Coverage of key truth-table corners
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===0 && ora===0 && X===0));
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===0 && ora===1 && X===0));
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===1 && ora===0 && X===0));
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===1 && A1===1 && A2===0 && A3===0 && X===1));
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===1 && A1===0 && A2===1 && A3===0 && X===1));
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===1 && A1===0 && A2===0 && A3===1 && X===1));
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===1 && ((A1&A2)||(A1&A3)||(A2&A3)) && X===1));
endmodule

bind sky130_fd_sc_lp__o31a sky130_fd_sc_lp__o31a_sva (.A1(A1),.A2(A2),.A3(A3),.B1(B1),.X(X));
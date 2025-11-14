// SVA for logic_expression
// Bindable, concise, and focused on functional equivalence, structure, and coverage

module logic_expression_sva (
  input logic A, B, C, D, E,
  input logic X,
  // bind to internal terms for structural checks
  input logic w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12
);
  // sample on any input change
  default clocking cb @(A or B or C or D or E); endclocking

  // known-inputs gating
  logic inputs_known;
  assign inputs_known = !$isunknown({A,B,C,D,E});

  // Golden function (from spec)
  function automatic logic f (input logic A,B,C,D,E);
    f = (~A & ~B & ~C &  D & ~E) |
        (~A & ~B & ~C &  D &  E) |
        (~A & ~B &  C & ~D &  E) |
        (~A & ~B &  C &  D &  E) |
        (~A &  B & ~C & ~D &  E) |
        (~A &  B & ~C &  D &  E) |
        (~A &  B &  C & ~D &  E) |
        ( A & ~B & ~C & ~D &  E) |
        ( A & ~B & ~C &  D &  E) |
        ( A & ~B &  C &  D &  E) |
        ( A &  B &  C & ~D &  E) |
        ( A &  B &  C &  D &  E);
  endfunction

  // Recompute minterms for one-hot and coverage
  logic m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12;
  assign m1  = (~A & ~B & ~C &  D & ~E);
  assign m2  = (~A & ~B & ~C &  D &  E);
  assign m3  = (~A & ~B &  C & ~D &  E);
  assign m4  = (~A & ~B &  C &  D &  E);
  assign m5  = (~A &  B & ~C & ~D &  E);
  assign m6  = (~A &  B & ~C &  D &  E);
  assign m7  = (~A &  B &  C & ~D &  E);
  assign m8  = ( A & ~B & ~C & ~D &  E);
  assign m9  = ( A & ~B & ~C &  D &  E);
  assign m10 = ( A & ~B &  C &  D &  E);
  assign m11 = ( A &  B &  C & ~D &  E);
  assign m12 = ( A &  B &  C &  D &  E);

  // Functional equivalence
  assert property (disable iff (!inputs_known) X == f(A,B,C,D,E));

  // X can only be 1 if E==1 or the unique (~E) minterm holds
  assert property (disable iff (!inputs_known) X |-> (E || m1));

  // Minterms are mutually exclusive (from inputs)
  logic [11:0] mvec;
  assign mvec = {m12,m11,m10,m9,m8,m7,m6,m5,m4,m3,m2,m1};
  assert property (disable iff (!inputs_known) $onehot0(mvec));

  // Structural checks on internal wires
  assert property (disable iff (!inputs_known) $onehot0({w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1}));
  assert property (disable iff (!inputs_known) w1  == m1);
  assert property (disable iff (!inputs_known) w2  == m2);
  assert property (disable iff (!inputs_known) w3  == m3);
  assert property (disable iff (!inputs_known) w4  == m4);
  assert property (disable iff (!inputs_known) w5  == m5);
  assert property (disable iff (!inputs_known) w6  == m6);
  assert property (disable iff (!inputs_known) w7  == m7);
  assert property (disable iff (!inputs_known) w8  == m8);
  assert property (disable iff (!inputs_known) w9  == m9);
  assert property (disable iff (!inputs_known) w10 == m10);
  assert property (disable iff (!inputs_known) w11 == m11);
  assert property (disable iff (!inputs_known) w12 == m12);

  // Basic X/Z check on output when inputs are known
  assert property (disable iff (!inputs_known) !$isunknown(X));

  // Coverage: each minterm, and both values of X
  genvar i;
  generate
    for (i=0;i<12;i++) begin : C_MINTERM
      cover property (inputs_known && mvec[i]);
    end
  endgenerate
  cover property (inputs_known && X);
  cover property (inputs_known && !X);

endmodule

bind logic_expression logic_expression_sva sva_i (
  .A(A), .B(B), .C(C), .D(D), .E(E), .X(X),
  .w1(w1), .w2(w2), .w3(w3), .w4(w4), .w5(w5), .w6(w6),
  .w7(w7), .w8(w8), .w9(w9), .w10(w10), .w11(w11), .w12(w12)
);
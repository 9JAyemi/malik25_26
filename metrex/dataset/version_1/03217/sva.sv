// SVA for four_bit_adder
module four_bit_adder_sva(
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] Sum,
  input  logic       Cout
);
  // Local expressions
  let P    = A ^ B;
  let G    = A & B;
  let add5 = {1'b0, A} + {1'b0, B} + Cin;

  let c1 = G[0] | (P[0] & Cin);
  let c2 = G[1] | (P[1] & c1);
  let c3 = G[2] | (P[2] & c2);
  let c4 = G[3] | (P[3] & c3);

  // X/Z checks
  assert property (@(*) !$isunknown({A,B,Cin,Sum,Cout}));

  // Functional equivalence (5-bit add)
  assert property (@(*) {Cout, Sum} == add5);

  // Bitwise FA decomposition
  assert property (@(*) Sum[0] == (P[0] ^ Cin));
  assert property (@(*) Sum[1] == (P[1] ^ c1));
  assert property (@(*) Sum[2] == (P[2] ^ c2));
  assert property (@(*) Sum[3] == (P[3] ^ c3));
  assert property (@(*) Cout    == c4);

  // Combinational stability (no unintended state)
  assert property (@(*) $stable({A,B,Cin}) |-> $stable({Sum,Cout}));

  // Corner-case sanity
  assert property (@(*) (B==4'h0 && !Cin) |-> (Sum==A && !Cout));
  assert property (@(*) (A==4'h0 && !Cin) |-> (Sum==B && !Cout));
  assert property (@(*) (A==~B && !Cin)   |-> (Sum==4'hF && !Cout));
  assert property (@(*) (A==~B &&  Cin)   |-> (Sum==4'h0 &&  Cout));

  // Coverage
  cover  property (@(*) (A==4'h0 && B==4'h0 && !Cin));
  cover  property (@(*) (A==4'hF && B==4'hF &&  Cin));
  cover  property (@(*) Cout);
  cover  property (@(*) c1);
  cover  property (@(*) c2);
  cover  property (@(*) c3);
  cover  property (@(*) c4);
  cover  property (@(*) (P==4'hF && Cin && Cout)); // full propagate ripple
endmodule

bind four_bit_adder four_bit_adder_sva sva_i(
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout)
);
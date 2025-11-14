// SVA for full_adder
module full_adder_sva(input logic A, B, Cin, Sum, Cout);
  let maj(a,b,c)  = (a & b) | (b & c) | (a & c);
  let xor3(a,b,c) = a ^ b ^ c;

  // Known outputs when inputs known
  assert property (@(A or B or Cin) (!$isunknown({A,B,Cin})) |-> (!$isunknown({Sum,Cout})));

  // Functional correctness
  assert property (@(A or B or Cin) Sum  == xor3(A,B,Cin));
  assert property (@(A or B or Cin) Cout == maj (A,B,Cin));

  // Compact functional coverage across popcount of inputs
  cover property (@(A or B or Cin) $countones({A,B,Cin}) == 0);
  cover property (@(A or B or Cin) $countones({A,B,Cin}) == 1);
  cover property (@(A or B or Cin) $countones({A,B,Cin}) == 2);
  cover property (@(A or B or Cin) $countones({A,B,Cin}) == 3);
endmodule

bind full_adder full_adder_sva fa_chk(.A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout));


// SVA for add4_carry (binds internal nets to check ripple structure)
module add4_carry_sva(
  input logic [3:0] A, B,
  input logic       Cin,
  input logic [3:0] Sum, S,
  input logic       Cout, C1, C2, C3
);
  let maj(a,b,c)  = (a & b) | (b & c) | (a & c);
  let xor3(a,b,c) = a ^ b ^ c;

  // Known outputs when inputs known
  assert property (@(A or B or Cin) (!$isunknown({A,B,Cin})) |-> (!$isunknown({Sum,Cout})));

  // End-to-end equivalence
  assert property (@(A or B or Cin) {Cout,Sum} == (A + B + Cin));

  // Bitwise ripple-carry structure
  assert property (@(A or B or Cin) S[0] == xor3(A[0],B[0],Cin));
  assert property (@(A or B or Cin) C1   == maj  (A[0],B[0],Cin));
  assert property (@(A or B or Cin) S[1] == xor3(A[1],B[1],C1));
  assert property (@(A or B or Cin) C2   == maj  (A[1],B[1],C1));
  assert property (@(A or B or Cin) S[2] == xor3(A[2],B[2],C2));
  assert property (@(A or B or Cin) C3   == maj  (A[2],B[2],C2));
  assert property (@(A or B or Cin) S[3] == xor3(A[3],B[3],C3));
  assert property (@(A or B or Cin) Cout == maj  (A[3],B[3],C3));
  assert property (@(A or B or Cin) Sum  == S);

  // Concise coverage: no-carry, carry, and full propagate chain
  cover property (@(A or B or Cin) (Cout == 0));
  cover property (@(A or B or Cin) (Cout == 1));
  cover property (@(A or B or Cin) (A == 4'hF && B == 4'h0 && Cin && Sum == 4'h0 && Cout));
endmodule

bind add4_carry add4_carry_sva add4_chk(
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout),
  .S(S), .C1(C1), .C2(C2), .C3(C3)
);
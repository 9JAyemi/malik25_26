// SVA checkers (bind to DUTs). Concise, full functional checks + key coverage.

module full_adder_sva (input logic A,B,Cin,S,Cout);
  // X-prop check: known inputs imply known outputs
  assert property (@(*) (!$isunknown({A,B,Cin})) |-> (!$isunknown({S,Cout})));

  // Functional equivalence
  assert property (@(*) {Cout,S} == A + B + Cin);

  // Input-space coverage (all 8 combinations)
  cover property (@(*) !$isunknown({A,B,Cin}) && {A,B,Cin}==3'b000);
  cover property (@(*) !$isunknown({A,B,Cin}) && {A,B,Cin}==3'b001);
  cover property (@(*) !$isunknown({A,B,Cin}) && {A,B,Cin}==3'b010);
  cover property (@(*) !$isunknown({A,B,Cin}) && {A,B,Cin}==3'b011);
  cover property (@(*) !$isunknown({A,B,Cin}) && {A,B,Cin}==3'b100);
  cover property (@(*) !$isunknown({A,B,Cin}) && {A,B,Cin}==3'b101);
  cover property (@(*) !$isunknown({A,B,Cin}) && {A,B,Cin}==3'b110);
  cover property (@(*) !$isunknown({A,B,Cin}) && {A,B,Cin}==3'b111);
endmodule

bind full_adder full_adder_sva fa_chk(.A(A),.B(B),.Cin(Cin),.S(S),.Cout(Cout));



module four_bit_adder_sva (
  input  logic [3:0] A,B,S,
  input  logic       Cin,Cout,
  // tap internal carries for structural checks
  input  logic       c1,c2,c3
);
  // X-prop check: known inputs imply known outputs
  assert property (@(*) (!$isunknown({A,B,Cin})) |-> (!$isunknown({S,Cout})));

  // Functional equivalence (golden: 5-bit sum)
  assert property (@(*) {Cout,S} == A + B + Cin);

  // Structural carry-chain correctness
  assert property (@(*) c1 == ((A[0]&B[0]) | (Cin & (A[0]^B[0]))));
  assert property (@(*) c2 == ((A[1]&B[1]) | (c1  & (A[1]^B[1]))));
  assert property (@(*) c3 == ((A[2]&B[2]) | (c2  & (A[2]^B[2]))));

  // Key corner-case coverage
  cover property (@(*) !$isunknown({A,B,Cin}) && (Cout==0));
  cover property (@(*) !$isunknown({A,B,Cin}) && (Cout==1));
  // full propagate chain (all bits propagate, carry ripples through)
  cover property (@(*) (&(A^B)) && Cin && Cout);
  // MSB generate (carry-out due to A[3]&B[3])
  cover property (@(*) (A[3]&B[3]) && Cout);
  // Boundary sums
  cover property (@(*) {A,B,Cin} == {4'h0,4'h0,1'b0});
  cover property (@(*) {A,B,Cin} == {4'hF,4'hF,1'b1});
endmodule

bind four_bit_adder four_bit_adder_sva fba_chk(
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout),
  .c1(c1), .c2(c2), .c3(c3)
);
// SVA checkers and binds for FullAdder and Adder4
// Uses $global_clock so no explicit clock is required.

checker FullAdder_sva(input logic a, b, cin, sum, cout);
  default clocking cb @($global_clock); endclocking

  // Correctness and X-protection when inputs are known
  assert property ( !$isunknown({a,b,cin})
                    |-> ( {cout,sum} == ({1'b0,a} + {1'b0,b} + cin)
                          && !$isunknown({sum,cout}) ) );

  // Full input-space coverage (8 combinations)
  cover property ( {a,b,cin} == 3'b000 );
  cover property ( {a,b,cin} == 3'b001 );
  cover property ( {a,b,cin} == 3'b010 );
  cover property ( {a,b,cin} == 3'b011 );
  cover property ( {a,b,cin} == 3'b100 );
  cover property ( {a,b,cin} == 3'b101 );
  cover property ( {a,b,cin} == 3'b110 );
  cover property ( {a,b,cin} == 3'b111 );
endchecker

bind FullAdder FullAdder_sva fa_sva (.*);


checker Adder4_sva(
  input logic [3:0] A, B,
  input logic       Cin,
  input logic [3:0] S,
  input logic       Cout,
  input logic       c1, c2, c3
);
  default clocking cb @($global_clock); endclocking

  // Top-level arithmetic equivalence and X-protection
  assert property ( !$isunknown({A,B,Cin})
                    |-> ( {Cout,S} == ({1'b0,A} + {1'b0,B} + Cin)
                          && !$isunknown({S,Cout,c1,c2,c3}) ) );

  // Internal ripple-carry correctness (majority function per stage)
  assert property ( !$isunknown({A[0],B[0],Cin}) |-> c1   == ((A[0]&B[0]) | (A[0]&Cin) | (B[0]&Cin)) );
  assert property ( !$isunknown({A[1],B[1],c1 }) |-> c2   == ((A[1]&B[1]) | (A[1]&c1 ) | (B[1]&c1 )) );
  assert property ( !$isunknown({A[2],B[2],c2 }) |-> c3   == ((A[2]&B[2]) | (A[2]&c2 ) | (B[2]&c2 )) );
  assert property ( !$isunknown({A[3],B[3],c3 }) |-> Cout == ((A[3]&B[3]) | (A[3]&c3 ) | (B[3]&c3 )) );

  // Optional per-bit sum checks (uncomment for additional internal checking)
  // assert property ( !$isunknown({A[0],B[0],Cin}) |-> S[0] == (A[0]^B[0]^Cin) );
  // assert property ( !$isunknown({A[1],B[1],c1 }) |-> S[1] == (A[1]^B[1]^c1 ) );
  // assert property ( !$isunknown({A[2],B[2],c2 }) |-> S[2] == (A[2]^B[2]^c2 ) );
  // assert property ( !$isunknown({A[3],B[3],c3 }) |-> S[3] == (A[3]^B[3]^c3 ) );

  // Broad functional coverage of key behaviors
  // Any legal add that matches the arithmetic spec
  cover property ( !$isunknown({A,B,Cin}) && ({Cout,S} == ({1'b0,A}+{1'b0,B}+Cin)) );

  // Extremes
  cover property ( {A,B,Cin} == {4'h0,4'h0,1'b0} );
  cover property ( {A,B,Cin} == {4'hF,4'hF,1'b1} );

  // Full propagate chain: A^B all ones with Cin=1 -> Cout=1
  cover property ( ((A^B)==4'hF) && Cin && Cout );

  // Per-stage generate with zero carry-in to that stage
  cover property ( (A[0]&B[0]) && !Cin && c1 );
  cover property ( (A[1]&B[1]) && !c1 && c2 );
  cover property ( (A[2]&B[2]) && !c2 && c3 );
  cover property ( (A[3]&B[3]) && !c3 && Cout );

  // Example kill at MSB: no generate at MSB and incoming carry gets killed
  cover property ( ~A[3] & ~B[3] & c3 & ~Cout );
endchecker

bind Adder4 Adder4_sva add4_sva (.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .c1(c1), .c2(c2), .c3(c3));
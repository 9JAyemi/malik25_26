// SVA for Ripple_Carry_Adder and Full_Adder
// Bind these checkers to the DUTs

module rca_sva; // bound into Ripple_Carry_Adder
  // Known-inputs => known-outputs
  assert property ( !$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout,sum,carry}) );

  // End-to-end arithmetic correctness
  assert property ( disable iff ($isunknown({A,B,Cin})) {Cout,S} == (A + B + Cin) );

  // Output wiring
  assert property ( S == sum );

  // Bit-slice correctness
  assert property ( sum[0] == (A[0]^B[0]^Cin) );
  assert property ( carry[0] == ((A[0]&B[0]) | (Cin & (A[0]^B[0]))) );

  assert property ( sum[1] == (A[1]^B[1]^carry[0]) );
  assert property ( carry[1] == ((A[1]&B[1]) | (carry[0] & (A[1]^B[1]))) );

  assert property ( sum[2] == (A[2]^B[2]^carry[1]) );
  assert property ( carry[2] == ((A[2]&B[2]) | (carry[1] & (A[2]^B[2]))) );

  assert property ( sum[3] == (A[3]^B[3]^carry[2]) );
  assert property ( Cout    == ((A[3]&B[3]) | (carry[2] & (A[3]^B[3]))) );

  // Functional coverage: extremes and ripple lengths
  cover property ( {Cout,S} == 5'd0 );   // 0
  cover property ( {Cout,S} == 5'd15 );  // 15 without carry
  cover property ( {Cout,S} == 5'd16 );  // exact overflow to 16
  cover property ( {Cout,S} == 5'd31 );  // max 31

  // Carry ripple length 0..4 from Cin
  cover property ( Cin && !(A[0]^B[0]) );
  cover property ( Cin &&  (A[0]^B[0]) && !(A[1]^B[1]) );
  cover property ( Cin &&  (A[0]^B[0]) &&  (A[1]^B[1]) && !(A[2]^B[2]) );
  cover property ( Cin &&  (A[0]^B[0]) &&  (A[1]^B[1]) &&  (A[2]^B[2]) && !(A[3]^B[3]) );
  cover property ( Cin &&  (A[0]^B[0]) &&  (A[1]^B[1]) &&  (A[2]^B[2]) &&  (A[3]^B[3]) );

  // Generate on edges
  cover property ( A[0] && B[0] );
  cover property ( A[3] && B[3] );
endmodule

module fa_sva; // bound into Full_Adder
  // Local correctness
  assert property ( disable iff ($isunknown({A,B,Cin})) S    == (A ^ B ^ Cin) );
  assert property ( disable iff ($isunknown({A,B,Cin})) Cout == ((A & B) | (Cin & (A ^ B))) );

  // Truth-table coverage (all 8 input combinations)
  cover property ( !A && !B && !Cin );
  cover property ( !A && !B &&  Cin );
  cover property ( !A &&  B && !Cin );
  cover property ( !A &&  B &&  Cin );
  cover property (  A && !B && !Cin );
  cover property (  A && !B &&  Cin );
  cover property (  A &&  B && !Cin );
  cover property (  A &&  B &&  Cin );
endmodule

bind Ripple_Carry_Adder rca_sva rca_sva_i();
bind Full_Adder         fa_sva  fa_sva_i();
// SVA for four_bit_adder and full_adder

`ifndef FOUR_BIT_ADDER_SVA
`define FOUR_BIT_ADDER_SVA

// Top-level checker
module four_bit_adder_assert
  (input logic [3:0] A,
   input logic [3:0] B,
   input logic [3:0] S,
   input logic       Cout,
   input logic [3:0] c);

  default clocking cb @(*); endclocking

  // Arithmetic correctness and X-protection
  assert property ( !$isunknown({A,B}) |-> {Cout,S} == A + B );
  assert property ( !$isunknown({A,B}) |-> !$isunknown({S,Cout,c}) );

  // Internal carry chain
  assert property ( c[0] == (A[0] & B[0]) );
  assert property ( c[1] == ((A[1]&B[1]) | (A[1]&c[0]) | (B[1]&c[0])) );
  assert property ( c[2] == ((A[2]&B[2]) | (A[2]&c[1]) | (B[2]&c[1])) );
  assert property ( Cout == ((A[3]&B[3]) | (A[3]&c[2]) | (B[3]&c[2])) );

  // Sum bits
  assert property ( S[0] == (A[0] ^ B[0]) );
  assert property ( S[1] == (A[1] ^ B[1] ^ c[0]) );
  assert property ( S[2] == (A[2] ^ B[2] ^ c[1]) );
  assert property ( S[3] == (A[3] ^ B[3] ^ c[2]) );

  // Functional coverage
  cover property ( !$isunknown({A,B}) && (c==4'b0000) && (Cout==1'b0) );         // no carries anywhere
  cover property ( !$isunknown({A,B}) && (Cout==1'b1) );                          // overflow
  cover property ( (A[0]&B[0]) && (A[1]^B[1]) && (A[2]^B[2]) && (A[3]^B[3]) && Cout ); // full ripple through MSB
  cover property ( c[0] && !c[1] );                                              // carry stops at bit1
  cover property ( c[0] && c[1] && !c[2] );                                      // carry stops at bit2
  cover property ( c[0] && c[1] && c[2] && !Cout );                              // ripple to MSB, killed there
  cover property ( A==4'd0  && B==4'd0  && {Cout,S}==5'd0 );                      // zero + zero
  cover property ( A==4'd15 && B==4'd15 && {Cout,S}==5'd30 );                     // max + max
endmodule

// Cell-level checker
module full_adder_assert
  (input logic a,b,cin,
   input logic sum, cout);

  default clocking cb @(*); endclocking

  assert property ( sum  == (a ^ b ^ cin) );
  assert property ( cout == ((a & b) | (a & cin) | (b & cin)) );
  assert property ( !$isunknown({a,b,cin}) |-> !$isunknown({sum,cout}) );

  // G/P/K coverage per cell
  cover property ( a & b );        // generate
  cover property ( !(a|b) );       // kill
  cover property ( (a ^ b) && cin ); // propagate with carry-in
endmodule

// Bindings
bind four_bit_adder four_bit_adder_assert i_four_bit_adder_assert (.A(A),.B(B),.S(S),.Cout(Cout),.c(c));
bind full_adder    full_adder_assert      i_full_adder_assert      (.a(a),.b(b),.cin(cin),.sum(sum),.cout(cout));

`endif
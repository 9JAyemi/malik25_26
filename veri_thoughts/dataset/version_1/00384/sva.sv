// SVA for full_adder and four_bit_adder (bindable, concise, high-quality)

module fa_sva (
  input logic A,
  input logic B,
  input logic Cin,
  input logic S,
  input logic Cout
);
  default clocking cb @(*) endclocking

  // Functional correctness (strongest check: sum equivalence)
  assert property ( {Cout,S} == ({1'b0,A} + {1'b0,B} + Cin) );

  // Redundant but direct-formula checks
  assert property ( S    == (A ^ B ^ Cin) );
  assert property ( Cout == ((A & B) | (Cin & (A ^ B))) );

  // Knownness: if inputs are 2-state, outputs must be 2-state
  assert property ( !$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout}) );

  // Coverage: all 8 input combinations
  cover property ( {A,B,Cin} == 3'b000 );
  cover property ( {A,B,Cin} == 3'b001 );
  cover property ( {A,B,Cin} == 3'b010 );
  cover property ( {A,B,Cin} == 3'b011 );
  cover property ( {A,B,Cin} == 3'b100 );
  cover property ( {A,B,Cin} == 3'b101 );
  cover property ( {A,B,Cin} == 3'b110 );
  cover property ( {A,B,Cin} == 3'b111 );
endmodule


module four_bit_adder_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       Cin,
  input logic [3:0] S,
  input logic       Cout,

  // internal signals (bind to these)
  input logic [3:0] S_int,
  input logic       C0,
  input logic       C1,
  input logic       C2
);
  default clocking cb @(*) endclocking

  function automatic logic cout_f (input logic a, b, cin);
    cout_f = (a & b) | (cin & (a ^ b));
  endfunction

  // End-to-end correctness
  assert property ( {Cout,S} == ({1'b0,A} + {1'b0,B} + Cin) );

  // Connectivity
  assert property ( S == S_int );

  // Bit-level ripple correctness (sum bits)
  assert property ( S_int[0] == (A[0] ^ B[0] ^ Cin) );
  assert property ( S_int[1] == (A[1] ^ B[1] ^ C0 ) );
  assert property ( S_int[2] == (A[2] ^ B[2] ^ C1 ) );
  assert property ( S_int[3] == (A[3] ^ B[3] ^ C2 ) );

  // Bit-level ripple correctness (carry chain)
  assert property ( C0    == cout_f(A[0], B[0], Cin) );
  assert property ( C1    == cout_f(A[1], B[1], C0 ) );
  assert property ( C2    == cout_f(A[2], B[2], C1 ) );
  assert property ( Cout  == cout_f(A[3], B[3], C2 ) );

  // Knownness: 2-state inputs imply 2-state outputs/internals
  assert property ( !$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout,S_int,C0,C1,C2}) );

  // Coverage:
  // - Full propagate chain with incoming carry (ripple through all stages)
  cover property ( (A ^ B) == 4'hF && Cin && Cout && (S == ~A) );

  // - Full propagate chain with no incoming carry (no carry out)
  cover property ( (A ^ B) == 4'hF && !Cin && !Cout );

  // - Carry generate somewhere causes carry out
  cover property ( ((A & B) != 4'h0) && Cout );
endmodule


// Bind assertions to DUTs
bind full_adder     fa_sva              u_fa_sva   (.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));
bind four_bit_adder four_bit_adder_sva  u_four_sva (.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout),
                                                   .S_int(S_int), .C0(C0), .C1(C1), .C2(C2));
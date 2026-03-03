// SVA for four_bit_adder and full_adder
// Bind these to the DUTs

module four_bit_adder_sva (input [3:0] A, B, input [3:0] S, input Cout);

  // Sample on any edge of inputs
  default clocking cb @(
      posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
      posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
      posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
      posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3]
  ); endclocking

  // Ignore checks when inputs are X/Z
  default disable iff ($isunknown({A,B}));

  // End-to-end correctness
  assert property ( {Cout, S} == ({1'b0, A} + {1'b0, B}) )
    else $error("Adder result mismatch: A=%0h B=%0h got {Cout,S}=%0h%0h", A, B, Cout, S);

  // Outputs must be known when inputs are known
  assert property ( !$isunknown({S, Cout}) )
    else $error("Outputs X/Z with known inputs: A=%0h B=%0h", A, B);

  // Simple corner implications
  assert property ( (A==4'h0) |-> (S==B && Cout==1'b0) );
  assert property ( (B==4'h0) |-> (S==A && Cout==1'b0) );

  // Coverage: key scenarios and ripple characteristics
  cover property (A==4'h0 && B==4'h0);
  cover property (A==4'hF && B==4'hF && Cout==1'b1 && S==4'hE);
  cover property (Cout==1'b0);
  cover property (Cout==1'b1);

  // Generate/propagate seen at each bit
  cover property (A[0] & B[0]); cover property (A[1] & B[1]);
  cover property (A[2] & B[2]); cover property (A[3] & B[3]);
  cover property (A[0] ^ B[0]); cover property (A[1] ^ B[1]);
  cover property (A[2] ^ B[2]); cover property (A[3] ^ B[3]);

  // Longest ripple: generate at bit0 and propagate through bits 1..3 -> Cout
  cover property ( (A[0] & B[0]) && &(A[3:1] ^ B[3:1]) && Cout );

endmodule


module full_adder_sva (input a, b, c_in, input s, c_out);

  // Sample on any edge of inputs
  default clocking fc @(
      posedge a or negedge a or posedge b or negedge b or
      posedge c_in or negedge c_in
  ); endclocking

  // Ignore checks when inputs are X/Z
  default disable iff ($isunknown({a,b,c_in}));

  // Truth table equivalence
  assert property ( s == (a ^ b ^ c_in) )
    else $error("FA sum mismatch a=%0b b=%0b c_in=%0b s=%0b", a,b,c_in,s);

  assert property ( c_out == ((a & b) | (a & c_in) | (b & c_in)) )
    else $error("FA carry mismatch a=%0b b=%0b c_in=%0b c_out=%0b", a,b,c_in,c_out);

  // Outputs must be known with known inputs
  assert property ( !$isunknown({s, c_out}) );

  // Coverage: all 8 input combinations
  cover property ( {a,b,c_in} == 3'b000 );
  cover property ( {a,b,c_in} == 3'b001 );
  cover property ( {a,b,c_in} == 3'b010 );
  cover property ( {a,b,c_in} == 3'b011 );
  cover property ( {a,b,c_in} == 3'b100 );
  cover property ( {a,b,c_in} == 3'b101 );
  cover property ( {a,b,c_in} == 3'b110 );
  cover property ( {a,b,c_in} == 3'b111 );

endmodule

// Bind to DUTs
bind four_bit_adder four_bit_adder_sva fba_sva (.*);
bind full_adder     full_adder_sva     fa_sva  (.*);
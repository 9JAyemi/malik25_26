// ------------------------------------------------------------
// SVA for four_bit_adder and full_adder (concise, high quality)
// Bind these modules to the DUTs to assert correctness and add coverage
// ------------------------------------------------------------

// Assertions bound into the 4-bit adder (checks sum, ripple carries, and internals)
module four_bit_adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout,
  input  logic [3:0] X,   // internal sums
  input  logic [3:0] C    // internal carries (C[0..2] used)
);
  // Core arithmetic equivalence and internal chain checks
  always_comb begin
    if (!$isunknown({A,B,Cin})) begin
      assert ({Cout,S} == A + B + Cin)
        else $error("Adder mismatch: {Cout,S} != A+B+Cin");

      // Internal net checks
      assert (S == X) else $error("S != X internal sum bus");

      assert (C[0] == ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
        else $error("Carry C[0] incorrect");
      assert (C[1] == ((A[1] & B[1]) | ((A[1] ^ B[1]) & C[0])))
        else $error("Carry C[1] incorrect");
      assert (C[2] == ((A[2] & B[2]) | ((A[2] ^ B[2]) & C[1])))
        else $error("Carry C[2] incorrect");
      assert (Cout == ((A[3] & B[3]) | ((A[3] ^ B[3]) & C[2])))
        else $error("Final carry Cout incorrect");

      // No-X on outputs when inputs are known
      assert (!$isunknown({S,Cout})) else $error("Outputs have X/Z with known inputs");
    end
  end

  // Lightweight functional coverage (key corners and ripple)
  always_comb begin
    if (!$isunknown({A,B,Cin})) begin
      cover (A==4'h0 && B==4'h0 && Cin==1'b0 && S==4'h0 && Cout==1'b0);           // zero
      cover (A==4'hF && B==4'hF && Cin==1'b0 && Cout==1'b1);                       // large + carry
      cover (Cin==1'b1);                                                            // Cin used
      cover (Cout==1'b1);                                                           // carry out observed
      cover ((A^B)==4'hF && Cin==1'b1 && Cout==1'b1);                               // full ripple propagate
      // Generate at each bit (seen sometime)
      cover (A[0]&B[0]); cover (A[1]&B[1]); cover (A[2]&B[2]); cover (A[3]&B[3]);
    end
  end
endmodule

// Assertions bound into each full_adder instance (local correctness)
module full_adder_sva (
  input  logic A,
  input  logic B,
  input  logic Cin,
  input  logic S,
  input  logic C
);
  always_comb begin
    if (!$isunknown({A,B,Cin})) begin
      assert (S == (A ^ B ^ Cin)) else $error("FA sum incorrect");
      assert (C == ((A & B) | ((A ^ B) & Cin))) else $error("FA carry incorrect");
      assert (!$isunknown({S,C})) else $error("FA outputs have X/Z with known inputs");
    end
  end

  // FA-level coverage of kill/generate/propagate behaviors
  always_comb begin
    if (!$isunknown({A,B,Cin})) begin
      cover (~A & ~B & ~Cin);          // kill
      cover (A & B & ~Cin);            // generate (no incoming carry)
      cover ((A ^ B) & Cin);           // propagate
    end
  end
endmodule

// ------------------------------------------------------------
// Bind directives (instantiate SVA in DUT scopes)
// ------------------------------------------------------------
bind four_bit_adder four_bit_adder_sva fba_sva (
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .X(X), .C(C)
);

bind full_adder full_adder_sva fa_sva (
  .A(A), .B(B), .Cin(Cin), .S(S), .C(C)
);
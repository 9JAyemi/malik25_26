// SVA checkers and binds for full_adder and adder_4bit

// Checker for 1-bit full_adder
module fa_sva(
  input logic A, B, Cin,
  input logic S, Cout
);
  // Functional correctness and X checking (when inputs are known)
  always_comb begin
    if (!$isunknown({A,B,Cin})) begin
      assert (S    === (A ^ B ^ Cin)) else $error("full_adder S mismatch");
      assert (Cout === ((A & B) | (Cin & (A ^ B)))) else $error("full_adder Cout mismatch");
      assert ({Cout,S} === (A + B + Cin)) else $error("full_adder {Cout,S} != A+B+Cin");
      assert (!$isunknown({S,Cout})) else $error("full_adder outputs X/Z with known inputs");
    end
  end

  // Cover all 8 input combinations
  always_comb if (!$isunknown({A,B,Cin})) begin
    cover ({A,B,Cin} == 3'b000);
    cover ({A,B,Cin} == 3'b001);
    cover ({A,B,Cin} == 3'b010);
    cover ({A,B,Cin} == 3'b011);
    cover ({A,B,Cin} == 3'b100);
    cover ({A,B,Cin} == 3'b101);
    cover ({A,B,Cin} == 3'b110);
    cover ({A,B,Cin} == 3'b111);
  end
endmodule

// Checker for 4-bit ripple-carry adder
module adder4_sva(
  input logic [3:0] A, B,
  input logic       Cin,
  input logic [3:0] S,
  input logic       Cout,
  // tap internal carries
  input logic       c1, c2, c3
);
  // Top-level arithmetic equivalence and per-stage checks
  always_comb begin
    if (!$isunknown({A,B,Cin})) begin
      // Full-width addition equivalence
      assert ({Cout,S} === (A + B + Cin)) else $error("adder_4bit sum mismatch");

      // Sum bits
      assert (S[0] === (A[0]^B[0]^Cin)) else $error("S[0] mismatch");
      assert (S[1] === (A[1]^B[1]^c1 )) else $error("S[1] mismatch");
      assert (S[2] === (A[2]^B[2]^c2 )) else $error("S[2] mismatch");
      assert (S[3] === (A[3]^B[3]^c3 )) else $error("S[3] mismatch");

      // Carry chain
      assert (c1   === ((A[0]&B[0]) | (Cin & (A[0]^B[0])))) else $error("c1 mismatch");
      assert (c2   === ((A[1]&B[1]) | (c1  & (A[1]^B[1])))) else $error("c2 mismatch");
      assert (c3   === ((A[2]&B[2]) | (c2  & (A[2]^B[2])))) else $error("c3 mismatch");
      assert (Cout === ((A[3]&B[3]) | (c3  & (A[3]^B[3])))) else $error("Cout mismatch");

      // Outputs not X/Z when inputs are known
      assert (!$isunknown({S,Cout,c1,c2,c3})) else $error("adder_4bit carries/outputs X/Z with known inputs");
    end
  end

  // Corner-case coverage
  always_comb if (!$isunknown({A,B,Cin})) begin
    cover (A==4'h0 && B==4'h0 && Cin==1'b0); // zero + zero
    cover (A==4'hF && B==4'h0 && Cin==1'b1); // full ripple from Cin
    cover (A==4'hF && B==4'hF && Cin==1'b1); // max + max + cin
    cover (A==4'hA && B==4'h5 && Cin==1'b0); // all propagate (A^B == 4'hF)
  end

  // Generate/propagate/kill seen at each bit
  genvar i;
  generate
    for (i=0;i<4;i++) begin : gpkg_cov
      always_comb if (!$isunknown({A[i],B[i]})) begin
        cover (A[i] & B[i]);          // generate
        cover (A[i] ^ B[i]);          // propagate
        cover (~A[i] & ~B[i]);        // kill
      end
    end
  endgenerate

  // Carry coverage
  always_comb if (!$isunknown({A,B,Cin})) begin
    cover (c1); cover (c2); cover (c3); cover (Cout);
    cover (!c1 && !c2 && !c3 && !Cout); // no carries
    cover (c1 && c2 && c3 && Cout);     // full ripple across all stages
  end
endmodule

// Bind the checkers to the DUTs
bind full_adder  fa_sva     u_fa_sva    (.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));
bind adder_4bit  adder4_sva u_adder4_sva(.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .c1(c1), .c2(c2), .c3(c3));
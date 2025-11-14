// SVA checkers for r4_adder and full_adder (concise, with coverage)
// Bind into DUTs; no DUT changes required.

module r4_adder_sva (
  input  [3:0] A, B,
  input        Cin,
  input  [3:0] S,
  input        Cout,
  // internal carries
  input        c1, c2, c3
);
  // Combinational equivalence and ripple-chain correctness
  always_comb begin
    assert ({Cout,S} == A + B + Cin)
      else $error("r4_adder sum mismatch A=%0h B=%0h Cin=%0b => got {Cout,S}=%0h", A, B, Cin, {Cout,S});

    // Bitwise sum/carry equations
    assert (S[0] == (A[0]^B[0]) ^ Cin);
    assert (c1   == (A[0]&B[0]) | ((A[0]^B[0]) & Cin));

    assert (S[1] == (A[1]^B[1]) ^ c1);
    assert (c2   == (A[1]&B[1]) | ((A[1]^B[1]) & c1));

    assert (S[2] == (A[2]^B[2]) ^ c2);
    assert (c3   == (A[2]&B[2]) | ((A[2]^B[2]) & c2));

    assert (S[3] == (A[3]^B[3]) ^ c3);
    assert (Cout == (A[3]&B[3]) | ((A[3]^B[3]) & c3));

    // X/Z propagation: clean outputs when inputs are 0/1
    if (!$isunknown({A,B,Cin})) assert (!$isunknown({S,Cout,c1,c2,c3}));

    // Functional coverage (key behaviors)
    cover (Cout==0);
    cover (Cout==1);
    cover (S==4'h0 && Cout==0);           // zero result, no carry
    cover (S==4'hF && Cout==1);           // max result with carry
    cover (&(A^B) && Cin && Cout);        // full propagate chain, ripple through
    cover (|(A&B));                        // any generate
    cover (~|A && ~|B && ~Cin);            // all zeros
    cover (&A && &B && Cin);               // all ones

    // Per-stage generate/kill evidence
    cover (A[0]&B[0] && c1);
    cover (~(A[0]|B[0]) && !c1);
    cover (A[1]&B[1] && c2);
    cover (~(A[1]|B[1]) && !c2);
    cover (A[2]&B[2] && c3);
    cover (~(A[2]|B[2]) && !c3);
    cover (A[3]&B[3] && Cout);
    cover (~(A[3]|B[3]) && !Cout);
  end
endmodule

bind r4_adder r4_adder_sva r4_adder_sva_i (.*);

// Optional: checker for the leaf full_adder as well
module full_adder_sva (
  input A, B, Cin,
  input S, Cout
);
  always_comb begin
    assert ({Cout,S} == A + B + Cin)
      else $error("full_adder mismatch A=%0b B=%0b Cin=%0b => {Cout,S}=%0b%0b", A, B, Cin, Cout, S);

    assert (S    == (A^B) ^ Cin);
    assert (Cout == (A&B) | ((A^B) & Cin));

    if (!$isunknown({A,B,Cin})) assert (!$isunknown({S,Cout}));

    cover (Cout==0); cover (Cout==1);
    cover ({A,B,Cin}==3'b000);
    cover ({A,B,Cin}==3'b111);
    cover ((A^B) && Cin && Cout);  // propagate-caused carry
    cover ((A&B) && Cout);         // generate-caused carry
  end
endmodule

bind full_adder full_adder_sva full_adder_sva_i (.*);
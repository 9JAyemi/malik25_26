// SVA for adder and full_adder (bindable, concise, high-quality checks)

module adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout,
  // internal nets
  input  logic       C1, C2, C3,
  input  logic       S0, S1, S2, S3
);
  always_comb begin
    // Golden model
    logic [4:0] exp = A + B + Cin;

    // Top-level correctness
    assert ((S == exp[3:0]) && (Cout == exp[4]))
      else $error("Adder mismatch: A=%0h B=%0h Cin=%0b S=%0h Cout=%0b exp=%0h",
                  A,B,Cin,S,Cout,exp);

    // Bitwise sum/carry chain (also checks ripple carries C1..C3 and S0..S3)
    logic expC1 = (A[0]&B[0]) | (Cin & (A[0]^B[0]));
    logic expS0 =  A[0]^B[0]^Cin;
    assert (S0 == expS0) else $error("S0 exp=%0b got=%0b", expS0, S0);
    assert (C1 == expC1) else $error("C1 exp=%0b got=%0b", expC1, C1);

    logic expS1 =  A[1]^B[1]^expC1;
    logic expC2 = (A[1]&B[1]) | (expC1 & (A[1]^B[1]));
    assert (S1 == expS1) else $error("S1 exp=%0b got=%0b", expS1, S1);
    assert (C2 == expC2) else $error("C2 exp=%0b got=%0b", expC2, C2);

    logic expS2 =  A[2]^B[2]^expC2;
    logic expC3 = (A[2]&B[2]) | (expC2 & (A[2]^B[2]));
    assert (S2 == expS2) else $error("S2 exp=%0b got=%0b", expS2, S2);
    assert (C3 == expC3) else $error("C3 exp=%0b got=%0b", expC3, C3);

    logic expS3 =  A[3]^B[3]^expC3;
    logic expCo = (A[3]&B[3]) | (expC3 & (A[3]^B[3]));
    assert (S3 == expS3) else $error("S3 exp=%0b got=%0b", expS3, S3);
    assert (Cout == expCo) else $error("Cout exp=%0b got=%0b", expCo, Cout);

    // Structural mapping
    assert (S == {S3,S2,S1,S0}) else $error("S concat mismatch");

    // Minimal yet meaningful coverage
    cover (Cout);
    cover (S == 4'h0);
    cover (S == 4'hF);
    cover (C1); cover (!C1);
    cover (C2); cover (!C2);
    cover (C3); cover (!C3);
    cover ({A[0],B[0],Cin} == 3'b000);
    cover ({A[0],B[0],Cin} == 3'b111);
  end
endmodule

bind adder adder_sva adder_sva_i (
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout),
  .C1(C1), .C2(C2), .C3(C3),
  .S0(S0), .S1(S1), .S2(S2), .S3(S3)
);


// Leaf-level SVA for full_adder (catches functional bugs and checks internal stages)
module full_adder_sva (
  input logic A, B, Cin,
  input logic S, Cout,
  // internal
  input logic X, Y, G, P
);
  always_comb begin
    logic expS  = A ^ B ^ Cin;
    logic expCo = (A & B) | (Cin & (A ^ B));

    // Functional truth table
    assert (S == expS)   else $error("FA S exp=%0b got=%0b", expS, S);
    assert (Cout == expCo) else $error("FA Cout exp=%0b got=%0b (A=%0b B=%0b Cin=%0b)",
                                       expCo, Cout, A, B, Cin);

    // Internal gate relationships
    assert (X == (A ^ B))    else $error("X mismatch");
    assert (Y == (A & B))    else $error("Y mismatch");
    assert (G == (X & Cin))  else $error("G mismatch");
    assert (P == (Y & Cin))  else $error("P mismatch");

    // Coverage
    cover (S);
    cover (Cout);
  end
endmodule

bind full_adder full_adder_sva full_adder_sva_i (
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout),
  .X(X), .Y(Y), .G(G), .P(P)
);
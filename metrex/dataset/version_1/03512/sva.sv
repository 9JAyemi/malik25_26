// SVA for half_adder, full_adder, and adder_4bit (bind-ready, concise and thorough)

module half_adder_sva(input A, input B, input S, input C);
  always_comb begin
    assert ({C,S} == A + B) else $error("half_adder sum/carry mismatch");
    // Truth-table coverage
    cover ({A,B}==2'b00);
    cover ({A,B}==2'b01);
    cover ({A,B}==2'b10);
    cover ({A,B}==2'b11);
  end
endmodule

module full_adder_sva(input A, input B, input Cin, input S, input Cout);
  logic expS, expC;
  always_comb begin
    expS = A ^ B ^ Cin;
    expC = (A & B) | (A & Cin) | (B & Cin);
    assert (S    == expS) else $error("full_adder S mismatch");
    assert (Cout == expC) else $error("full_adder Cout mismatch");
    assert ({Cout,S} == (A + B + Cin)) else $error("full_adder packed sum mismatch");
    // Input-space coverage
    cover ({A,B,Cin}==3'b000); cover ({A,B,Cin}==3'b001);
    cover ({A,B,Cin}==3'b010); cover ({A,B,Cin}==3'b011);
    cover ({A,B,Cin}==3'b100); cover ({A,B,Cin}==3'b101);
    cover ({A,B,Cin}==3'b110); cover ({A,B,Cin}==3'b111);
  end
endmodule

module adder_4bit_sva(
  input [3:0] A, input [3:0] B, input Cin,
  input [3:0] S, input Cout,
  input [3:0] C, input [2:0] S1
);
  logic [4:0] exp_sum;
  always_comb begin
    exp_sum = {1'b0,A} + {1'b0,B} + Cin;
    assert ({Cout,S} == exp_sum) else $error("adder_4bit result mismatch vs A+B+Cin");

    // Ripple-chain local checks
    assert (S[0] == (A[0]^B[0])) else $error("bit0 sum mismatch");
    assert (C[0] == (A[0]&B[0])) else $error("bit0 carry mismatch");

    assert (S1[0] == (A[1]^B[1]^C[0])) else $error("bit1 sum mismatch");
    assert (C[1]  == ((A[1]&B[1])|(A[1]&C[0])|(B[1]&C[0]))) else $error("bit1 carry mismatch");

    assert (S1[1] == (A[2]^B[2]^C[1])) else $error("bit2 sum mismatch");
    assert (C[2]  == ((A[2]&B[2])|(A[2]&C[1])|(B[2]&C[1]))) else $error("bit2 carry mismatch");

    assert (S[3]  == (A[3]^B[3]^C[2])) else $error("bit3 sum mismatch");
    assert (Cout  == ((A[3]&B[3])|(A[3]&C[2])|(B[3]&C[2]))) else $error("bit3 carry mismatch");

    // Output mapping consistency (detects wiring/concat issues)
    assert (S[1] == S1[0]) else $error("S[1] != S1[0]");
    assert (S[2] == S1[1]) else $error("S[2] != S1[1]");

    // X/Z checks
    assert (!$isunknown({Cout,S})) else $error("adder_4bit X/Z on outputs");

    // Useful coverage
    cover (Cin==1'b0);
    cover (Cin==1'b1);
    cover (Cout==1'b0);
    cover (Cout==1'b1);
    cover (A==4'h0 && B==4'h0 && Cin==1'b0);
    cover (A==4'hF && B==4'hF && Cin==1'b1);
    // Propagate/generate scenarios
    cover ((A^B)==4'hF);               // full propagate pattern
    cover (((A&B)&4'hE)!=0);           // any generate on bits [3:1]
  end
endmodule

// Binds
bind half_adder  half_adder_sva  ha_sva (.A(A), .B(B), .S(S), .C(C));
bind full_adder  full_adder_sva  fa_sva (.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));
bind adder_4bit  adder_4bit_sva  a4_sva (.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .C(C), .S1(S1));
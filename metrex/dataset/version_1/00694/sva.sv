// SVA for full_adder and binary_multiplier
// Concise, bound checkers with strong functional checks and focused coverage

// Full-adder checker
module full_adder_asserts (
  input logic A, B, cin,
  input logic sum, cout
);
  // Functional correctness
  always_comb begin
    assert (sum === (A ^ B ^ cin)) else $error("full_adder: sum mismatch A=%0b B=%0b cin=%0b sum=%0b",A,B,cin,sum);
    assert (cout === ((A & B) | (cin & (A ^ B)))) else $error("full_adder: cout mismatch A=%0b B=%0b cin=%0b cout=%0b",A,B,cin,cout);
    if (!$isunknown({A,B,cin})) assert (!$isunknown({sum,cout})) else $error("full_adder: X/Z on outputs with known inputs");
  end

  // Input space coverage (all 8 combinations), plus output toggles
  always_comb begin
    cover ({A,B,cin}==3'b000);
    cover ({A,B,cin}==3'b001);
    cover ({A,B,cin}==3'b010);
    cover ({A,B,cin}==3'b011);
    cover ({A,B,cin}==3'b100);
    cover ({A,B,cin}==3'b101);
    cover ({A,B,cin}==3'b110);
    cover ({A,B,cin}==3'b111);
    cover (sum==1'b0); cover (sum==1'b1);
    cover (cout==1'b0); cover (cout==1'b1);
  end
endmodule

bind full_adder full_adder_asserts fa_sva(.A(A),.B(B),.cin(cin),.sum(sum),.cout(cout));


// 4x4 multiplier checker
module binary_multiplier_asserts (
  input  logic [3:0] A, B,
  input  logic [7:0] P,
  // tap internals to check row arithmetic
  input  logic [3:0] S0, S1, S2, S3,
  input  logic [3:0] C0, C1, C2, C3
);
  // Top-level golden functionality
  always_comb begin
    assert (P === (A * B)) else $error("mult: P!=A*B A=%0d B=%0d P=%0d ref=%0d", A, B, P, A*B);
    if (!$isunknown({A,B})) assert (!$isunknown(P)) else $error("mult: X/Z on P with known inputs");

    // Sanity corner cases
    if ((A==0) || (B==0)) assert (P==0) else $error("mult: zero operand rule fail A=%0d B=%0d P=%0d",A,B,P);
    if (A==1) assert (P==B) else $error("mult: identity fail A=1 B=%0d P=%0d",B,P);
    if (B==1) assert (P==A) else $error("mult: identity fail B=1 A=%0d P=%0d",A,P);

    // Check each ripple-adder row arithmetic (connectivity/carry-chain)
    assert ({C0[3], S0} === (A + {4{B[0]}})) else $error("mult: row0 mismatch");
    assert ({C1[3], S1} === (A + {4{B[1]}})) else $error("mult: row1 mismatch");
    assert ({C2[3], S2} === (A + {4{B[2]}})) else $error("mult: row2 mismatch");
    assert ({C3[3], S3} === (A + {4{B[3]}})) else $error("mult: row3 mismatch");
  end

  // Focused coverage of key scenarios
  always_comb begin
    cover (A==0 && B==0 && P==0);
    cover (A==0 && B!=0 && P==0);
    cover (A!=0 && B==0 && P==0);
    cover (A==1 && P==B);
    cover (B==1 && P==A);
    cover (A==4'hF && B==4'hF && P==8'hE1); // 15*15=225
    cover (P[7]==1'b1); // MSB set
    cover (P[0]==1'b1); // LSB set
  end
endmodule

bind binary_multiplier binary_multiplier_asserts bm_sva(
  .A(A), .B(B), .P(P),
  .S0(S0), .S1(S1), .S2(S2), .S3(S3),
  .C0(C0), .C1(C1), .C2(C2), .C3(C3)
);
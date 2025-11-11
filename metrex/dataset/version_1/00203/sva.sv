// SVA checkers for ripple_carry_adder and full_adder
// Focused, high-quality properties with concise coverage.
// Bind these into the DUTs.

//////////////////////////////////////////////////////////
// Checker for the 4-bit ripple-carry adder
//////////////////////////////////////////////////////////
module rca_checker (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout,
  input  logic [3:0] C   // internal carry chain (C[2:0] used)
);
  // Evaluate on any change (combinational)
  // Assertions
  assert property (@(*) !$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout,C[2:0]}))
    else $error("X/Z detected on outputs with known inputs");

  // End-to-end arithmetic correctness
  assert property (@(*) {Cout,S} == ({1'b0,A} + {1'b0,B} + Cin))
    else $error("Adder result mismatch: {Cout,S} != A+B+Cin");

  // Bit-slice functional and chain connectivity checks
  // LSB
  assert property (@(*)
    S[0] == (A[0]^B[0]^Cin) &&
    C[0] == ((A[0]&B[0]) | (A[0]&Cin) | (B[0]&Cin)))
    else $error("Bit0 sum/carry incorrect");

  // Middle bits
  genvar i;
  generate
    for (i=1; i<=2; i++) begin : g_mid
      assert property (@(*)
        S[i] == (A[i]^B[i]^C[i-1]) &&
        C[i] == ((A[i]&B[i]) | (A[i]&C[i-1]) | (B[i]&C[i-1])))
        else $error("Bit%0d sum/carry incorrect", i);
    end
  endgenerate

  // MSB (carry out)
  assert property (@(*)
    S[3] == (A[3]^B[3]^C[2]) &&
    Cout == ((A[3]&B[3]) | (A[3]&C[2]) | (B[3]&C[2])))
    else $error("Bit3 sum/carry (Cout) incorrect");

  // Minimal but meaningful coverage
  // - Cover all possible 5-bit results {Cout,S} (0..31)
  generate
    genvar k;
    for (k=0; k<32; k++) begin : g_res_cov
      localparam logic [4:0] RES = k[4:0];
      cover property (@(*) {Cout,S} == RES);
    end
  endgenerate

  // - Cover no-carry and full-carry overflow corner cases
  cover property (@(*) ({Cout,S} == 5'b0_0000)); // sum=0, no carry
  cover property (@(*) ({Cout,S} == 5'b1_0000)); // overflow with zero sum

  // - Cover full propagate chain (all bits propagate carry)
  cover property (@(*) ((A^B)==4'hF && Cin && Cout));
endmodule

bind ripple_carry_adder rca_checker rca_chk (
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .C(C)
);

//////////////////////////////////////////////////////////
// Checker for a single full_adder
//////////////////////////////////////////////////////////
module fa_checker (
  input logic A,
  input logic B,
  input logic Cin,
  input logic S,
  input logic C
);
  // No X/Z on outputs if inputs are known
  assert property (@(*) !$isunknown({A,B,Cin}) |-> !$isunknown({S,C}))
    else $error("Full adder outputs X/Z with known inputs");

  // Truth-function checks
  assert property (@(*) S == (A ^ B ^ Cin))
    else $error("Full adder S incorrect");
  assert property (@(*) C == ((A & B) | (A & Cin) | (B & Cin)))
    else $error("Full adder C incorrect");

  // Cover all 8 input combinations
  generate
    genvar m;
    for (m=0; m<8; m++) begin : g_fa_cov
      localparam logic [2:0] V = m[2:0];
      cover property (@(*) {A,B,Cin} == V);
    end
  endgenerate
endmodule

bind full_adder fa_checker fa_chk (.*);
// SVA for four_bit_adder and full_adder
// Concise, full functional checks + key internal coverage

// Checker for the 4-bit ripple-carry adder
module four_bit_adder_sva(
  input  logic [3:0] A, B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout,
  // internal carries
  input  logic       C1, C2, C3
);
  default clocking cb @(*); endclocking

  function automatic logic carry3(logic a,b,cin);
    return (a & b) | (a & cin) | (b & cin);
  endfunction
  function automatic logic sum3(logic a,b,cin);
    return a ^ b ^ cin;
  endfunction

  // Top-level arithmetic equivalence (allow design to settle with ##0)
  assert property (##0 {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin))
    else $error("4-bit adder sum/carry mismatch");

  // Bitwise sums and carries through the ripple chain
  assert property (##0 S[0] == sum3(A[0], B[0], Cin));
  assert property (##0 C1   == carry3(A[0], B[0], Cin));
  assert property (##0 S[1] == sum3(A[1], B[1], C1));
  assert property (##0 C2   == carry3(A[1], B[1], C1));
  assert property (##0 S[2] == sum3(A[2], B[2], C2));
  assert property (##0 C3   == carry3(A[2], B[2], C2));
  assert property (##0 S[3] == sum3(A[3], B[3], C3));
  assert property (##0 Cout == carry3(A[3], B[3], C3));

  // X/Z checks: clean outputs when inputs are known
  assert property (!$isunknown({A,B,Cin}) |-> ##0 !$isunknown({S,Cout,C1,C2,C3}));

  // Key coverage: zero, overflow, full propagate, internal generate
  cover property (A==4'h0 && B==4'h0 && Cin==1'b0 && S==4'h0 && Cout==1'b0);
  cover property (A==4'hF && B==4'hF && Cin==1'b1 && S==4'hF && Cout==1'b1); // 31 = 1_1111
  cover property (A==4'hF && B==4'h0 && Cin==1'b1 && S==4'h0 && C1 && C2 && C3 && Cout); // pure propagate
  cover property (A==4'b0010 && B==4'b0010 && Cin==1'b0 && !C1 && C2); // internal generate at bit1
endmodule

// Checker for a single full_adder cell
module full_adder_sva(
  input  logic A, B, carry_in,
  input  logic sum, carry_out
);
  default clocking @(*); endclocking

  // Functional equivalence
  assert property (##0 sum       == (A ^ B ^ carry_in));
  assert property (##0 carry_out == ((A & B) | (A & carry_in) | (B & carry_in)));

  // X/Z checks
  assert property (!$isunknown({A,B,carry_in}) |-> ##0 !$isunknown({sum,carry_out}));

  // Minimal, meaningful coverage: kill, generate, propagate
  cover property (A==1'b0 && B==1'b0 && carry_in==1'b1 && sum==1'b1 && carry_out==1'b0); // kill
  cover property (A==1'b1 && B==1'b1 && carry_in==1'b0 && carry_out==1'b1);              // generate
  cover property (A==1'b1 && B==1'b0 && carry_in==1'b1 && carry_out==1'b1 && sum==1'b0); // propagate
endmodule

// Bind into DUTs
bind four_bit_adder four_bit_adder_sva sva4 (
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout),
  .C1(C1), .C2(C2), .C3(C3)
);

bind full_adder full_adder_sva svafa (
  .A(A), .B(B), .carry_in(carry_in),
  .sum(sum), .carry_out(carry_out)
);
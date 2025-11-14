// SVA for full_adder
module sva_full_adder(input logic A, B, CI, S, CO);
  default clocking cb @(*); endclocking

  // Functional correctness
  assert property (S  == (A ^ B ^ CI)) else $error("full_adder S mismatch");
  assert property (CO == ((A & B) | (CI & (A ^ B)))) else $error("full_adder CO mismatch");

  // Clean outputs when inputs known
  assert property (!$isunknown({A,B,CI}) |-> !$isunknown({S,CO}))
    else $error("full_adder X/Z on outputs with known inputs");

  // Input-space coverage (all 8 combinations)
  cover property (A==0 && B==0 && CI==0);
  cover property (A==0 && B==0 && CI==1);
  cover property (A==0 && B==1 && CI==0);
  cover property (A==0 && B==1 && CI==1);
  cover property (A==1 && B==0 && CI==0);
  cover property (A==1 && B==0 && CI==1);
  cover property (A==1 && B==1 && CI==0);
  cover property (A==1 && B==1 && CI==1);
endmodule

bind full_adder sva_full_adder svafa(.A(A),.B(B),.CI(CI),.S(S),.CO(CO));


// SVA for four_bit_adder (checks ripple chain, sum, mapping)
module sva_four_bit_adder(
  input  logic [3:0] A, B,
  input  logic [3:0] S,
  input  logic [3:0] CO_int,
  input  logic [4:0] C,
  input  logic       CO
);
  default clocking cb @(*); endclocking

  // Top-level arithmetic correctness and mapping
  assert property ({CO,S} == (A + B)) else $error("four_bit_adder sum mismatch");
  assert property (C == {CO,S}) else $error("four_bit_adder C bus mapping mismatch");

  // Stage 0 (CI=0)
  assert property (S[0] == (A[0] ^ B[0])) else $error("S[0] mismatch");
  assert property (CO_int[0] == (A[0] & B[0])) else $error("CO_int[0] mismatch");
  // Generate/Kill classification at bit0
  assert property ((A[0]&B[0]) |-> CO_int[0]) else $error("bit0 generate failed");
  assert property ((~A[0]&~B[0]) |-> !CO_int[0]) else $error("bit0 kill failed");

  // Bits 1..2 internal ripple
  genvar i;
  generate
    for (i=1; i<=2; i++) begin : g_mid
      assert property (S[i] == (A[i]^B[i]^CO_int[i-1])) else $error("S[%0d] mismatch", i);
      assert property (CO_int[i] == ((A[i]&B[i]) | (CO_int[i-1] & (A[i]^B[i]))))
        else $error("CO_int[%0d] mismatch", i);

      // Generate/Propagate/Kill behavior
      assert property ((A[i]&B[i]) |-> CO_int[i]) else $error("bit%0d generate failed", i);
      assert property ((~A[i]&~B[i]) |-> !CO_int[i]) else $error("bit%0d kill failed", i);
      assert property ((A[i]^B[i]) |-> (CO_int[i] == CO_int[i-1]))
        else $error("bit%0d propagate failed", i);
    end
  endgenerate

  // MSB stage (bit3) with final CO
  assert property (S[3] == (A[3]^B[3]^CO_int[2])) else $error("S[3] mismatch");
  assert property (CO    == ((A[3]&B[3]) | (CO_int[2] & (A[3]^B[3]))))
    else $error("CO mismatch");
  assert property ((A[3]&B[3]) |-> CO) else $error("bit3 generate failed");
  assert property ((~A[3]&~B[3]) |-> !CO) else $error("bit3 kill failed");
  assert property ((A[3]^B[3]) |-> (CO == CO_int[2])) else $error("bit3 propagate failed");

  // Clean outputs when inputs known
  assert property (!$isunknown({A,B}) |-> !$isunknown({S,CO,C,CO_int}))
    else $error("four_bit_adder X/Z on outputs with known inputs");

  // Coverage: extremes, overflow, long propagate chain
  cover property (A==4'h0 && B==4'h0 && C==5'd0);
  cover property (A==4'hF && B==4'hF && CO && C==5'd30);
  cover property (A==4'hF && B==4'h1 && CO); // long propagate (bits 1..3)
  cover property (CO);                       // any overflow
  // Basic toggle coverage on key signals
  cover property ($rose(CO));  cover property ($fell(CO));
  cover property ($rose(S[0])); cover property ($rose(S[3]));
endmodule

bind four_bit_adder sva_four_bit_adder svafba(.A(A),.B(B),.S(S),.CO_int(CO_int),.C(C),.CO(CO));
// SVA for nor4b_with_inverting_input
// Function: Y = ~(A | B | C | ~D_N) == (~A & ~B & ~C & D_N)
// Concise, high-quality checks + full 4-input truth-table coverage.

module nor4b_with_inverting_input_sva (input A, B, C, D_N, Y);

  // Sample on any input change to catch combinational behavior
  default clocking cb @(
      posedge A or negedge A or
      posedge B or negedge B or
      posedge C or negedge C or
      posedge D_N or negedge D_N
  ); endclocking

  // Core functional equivalence (4-state safe)
  assert property (Y === ((~A) & (~B) & (~C) & D_N))
    else $error("nor4b_with_inverting_input: functional mismatch Y vs (~A & ~B & ~C & D_N), A=%b B=%b C=%b D_N=%b Y=%b", A,B,C,D_N,Y);

  // Strong directional checks (robust to Xs on unused inputs)
  // Any of A/B/C high must force Y low
  assert property ((A===1 || B===1 || C===1) |-> (Y===0))
    else $error("nor4b_with_inverting_input: A/B/C high did not force Y low, A=%b B=%b C=%b D_N=%b Y=%b", A,B,C,D_N,Y);
  // When A=B=C=0, Y should mirror D_N
  assert property (((A===0)&&(B===0)&&(C===0)) |-> (Y===D_N))
    else $error("nor4b_with_inverting_input: With A=B=C=0, Y != D_N, D_N=%b Y=%b", D_N, Y);
  // If Y is high, inputs must be uniquely 0001 (A,B,C,D_N)
  assert property ((Y===1) |-> ((A===0)&&(B===0)&&(C===0)&&(D_N===1)))
    else $error("nor4b_with_inverting_input: Y high without 0001 on (A,B,C,D_N), A=%b B=%b C=%b D_N=%b", A,B,C,D_N);

  // Full truth-table coverage (all 16 input combinations, with expected Y)
  cover property ((A==0 && B==0 && C==0 && D_N==0) && (Y==0));
  cover property ((A==0 && B==0 && C==0 && D_N==1) && (Y==1));
  cover property ((A==0 && B==0 && C==1 && D_N==0) && (Y==0));
  cover property ((A==0 && B==0 && C==1 && D_N==1) && (Y==0));
  cover property ((A==0 && B==1 && C==0 && D_N==0) && (Y==0));
  cover property ((A==0 && B==1 && C==0 && D_N==1) && (Y==0));
  cover property ((A==0 && B==1 && C==1 && D_N==0) && (Y==0));
  cover property ((A==0 && B==1 && C==1 && D_N==1) && (Y==0));
  cover property ((A==1 && B==0 && C==0 && D_N==0) && (Y==0));
  cover property ((A==1 && B==0 && C==0 && D_N==1) && (Y==0));
  cover property ((A==1 && B==0 && C==1 && D_N==0) && (Y==0));
  cover property ((A==1 && B==0 && C==1 && D_N==1) && (Y==0));
  cover property ((A==1 && B==1 && C==0 && D_N==0) && (Y==0));
  cover property ((A==1 && B==1 && C==0 && D_N==1) && (Y==0));
  cover property ((A==1 && B==1 && C==1 && D_N==0) && (Y==0));
  cover property ((A==1 && B==1 && C==1 && D_N==1) && (Y==0));

endmodule

// Bind into DUT
bind nor4b_with_inverting_input nor4b_with_inverting_input_sva (.A(A), .B(B), .C(C), .D_N(D_N), .Y(Y));
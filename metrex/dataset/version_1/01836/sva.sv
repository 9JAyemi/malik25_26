// SVA for magnitude_comparator_4bit and its pipeline stages
// Concise, end-to-end functional checks, internal consistency, and coverage.

///////////////////////////////////////////////
// Top-level DUT end-to-end functional SVA  //
///////////////////////////////////////////////
module mc_top_sva (
  input  logic [3:0] A, B,
  input  logic       EQ, GT, LT,
  input  logic       EQ_int, GT_int, LT_int
);
  // Functional correctness vs. true 4-bit unsigned magnitude compare
  ap_func_eq: assert property (@(*) (EQ == (A == B)));
  ap_func_gt: assert property (@(*) (GT == (A >  B)));
  ap_func_lt: assert property (@(*) (LT == (A <  B)));

  // Exactly one outcome true
  ap_onehot:  assert property (@(*) $onehot({EQ,GT,LT}));

  // Internal wires match outputs
  ap_int_map: assert property (@(*) (EQ==EQ_int && GT==GT_int && LT==LT_int));

  // No X/Z on outputs when inputs are known
  ap_no_x:    assert property (@(*) (!$isunknown({A,B})) |-> !$isunknown({EQ,GT,LT}));

  // Coverage of each result and key corners
  cp_eq:      cover property (@(*) (A==B && EQ));
  cp_gt:      cover property (@(*) (A> B && GT));
  cp_lt:      cover property (@(*) (A< B && LT));
  cp_minmax1: cover property (@(*) (A==4'd0  && B==4'd15 && LT));
  cp_minmax2: cover property (@(*) (A==4'd15 && B==4'd0  && GT));
endmodule

///////////////////////////////////////////////
// Stage 1 internal-computation SVA          //
///////////////////////////////////////////////
module stage1_sva (
  input logic [3:0] A, B,
  input logic [4:0] sum
);
  // Bit-accurate checks to the intended combinational equations
  a_s0: assert property (@(*) sum[0] == (A[0]^B[0]));
  a_s1: assert property (@(*) sum[1] == ((A[1]^B[1]) ^ (A[0]&B[0])));
  a_s2: assert property (@(*) sum[2] == ((A[2]^B[2]) ^ (A[1]&B[1])));
  a_s3: assert property (@(*) sum[3] == (A[2]&B[2]));
  a_s4: assert property (@(*) sum[4] == (A[3]^B[3]));

  // No X/Z on sum when inputs are known
  a_no_x: assert property (@(*) (!$isunknown({A,B})) |-> !$isunknown(sum));

  // Coverage of useful internal patterns
  c_sum_zero: cover property (@(*) (sum == 5'b0));
  c_sum_msb1: cover property (@(*) sum[4]);
endmodule

///////////////////////////////////////////////
// Stage 2 mapping from sum to outputs SVA   //
///////////////////////////////////////////////
module stage2_sva (
  input logic [4:0] sum,
  input logic       EQ, GT, LT
);
  logic [4:0] sum_abs;
  assign sum_abs = (sum[4] == 1) ? (~sum + 5'b1) : sum;

  // Check conformance to implemented mapping
  a_eq: assert property (@(*) (EQ == (sum_abs == 5'b0)));
  a_gt: assert property (@(*) (GT == (sum_abs[4] == 1'b0)));
  a_lt: assert property (@(*) (LT == (sum_abs[4] == 1'b1)));

  // Outcomes remain exclusive
  a_onehot: assert property (@(*) $onehot({EQ,GT,LT}));

  // If abs==0, only EQ is 1
  a_zero_only_eq: assert property (@(*) ((sum_abs==5'b0) |-> (EQ && !GT && !LT)));

  // No X/Z on outputs when sum known
  a_no_x: assert property (@(*) (!$isunknown(sum)) |-> !$isunknown({EQ,GT,LT}));

  // Coverage of both branches and zero
  c_zero: cover property (@(*) (sum_abs==5'b0 && EQ));
  c_msb1: cover property (@(*) (sum_abs[4] && LT));
endmodule

/////////////////////////////////////////////////////
// Bind assertions into the DUT and submodules     //
/////////////////////////////////////////////////////
bind magnitude_comparator_4bit mc_top_sva   u_mc_top_sva   (.A(A), .B(B), .EQ(EQ), .GT(GT), .LT(LT), .EQ_int(EQ_int), .GT_int(GT_int), .LT_int(LT_int));
bind pipeline_stage1           stage1_sva   u_stage1_sva    (.A(A), .B(B), .sum(sum));
bind pipeline_stage2           stage2_sva   u_stage2_sva    (.sum(sum), .EQ(EQ), .GT(GT), .LT(LT));
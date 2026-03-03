// SVA for adder — concise, high-quality checks and coverage
// Bind this to the DUT: bind adder adder_sva #(8) sva_i (.*);

module adder_sva #(parameter int W = 8)
(
  input  logic signed [W-1:0] A,
  input  logic signed [W-1:0] B,
  input  logic signed [W-1:0] sum,
  input  logic                C
);

  // Helper constants for coverage
  localparam logic signed [W-1:0] MAX = {1'b0, {(W-1){1'b1}}}; // +2^(W-1)-1
  localparam logic signed [W-1:0] MIN = {1'b1, {(W-1){1'b0}}}; // -2^(W-1)

  // 1) Outputs are fully determined by inputs (no X/Z when inputs known)
  ap_known_out: assert property (@(A or B)
                                 !$isunknown({A,B}) |-> ##0 !$isunknown({sum,C}))
    else $error("adder: X/Z on outputs with known inputs");

  // 2) Functional correctness: 9-bit packed sum must equal signed A+B
  ap_full_sum:  assert property (@(A or B)
                                 !$isunknown({A,B}) |-> ##0 {C,sum} == ($signed(A)+$signed(B)))
    else $error("adder: {C,sum} != signed(A)+signed(B)");

  // 3) Signed-overflow relationship: C^sum[MSB] indicates overflow for signed add
  ap_sovf_rel:  assert property (@(A or B)
                                 !$isunknown({A,B}) |-> ##0
                                 (C ^ sum[W-1]) == (( A[W-1] &  B[W-1] & ~sum[W-1]) |
                                                    (~A[W-1] & ~B[W-1] &  sum[W-1])))
    else $error("adder: signed-overflow relation violated");

  // Optional sanity: opposite-sign add implies no signed overflow
  ap_opp_sign_no_ovf: assert property (@(A or B)
                                       !$isunknown({A,B}) |-> ##0
                                       (A[W-1] ^ B[W-1]) |-> (C == sum[W-1]))
    else $error("adder: opposite-sign add should not overflow");

  // -------- Coverage --------
  // Positive overflow: + + -> negative result bit
  cv_pos_ovf:  cover property (@(A or B) !$isunknown({A,B}) ##0
                               ( A[W-1]==0 && B[W-1]==0 && sum[W-1]==1 ));

  // Negative overflow: - - -> positive result bit
  cv_neg_ovf:  cover property (@(A or B) !$isunknown({A,B}) ##0
                               ( A[W-1]==1 && B[W-1]==1 && sum[W-1]==0 ));

  // Opposite-sign addition (no overflow expected)
  cv_opp_sign: cover property (@(A or B) !$isunknown({A,B}) ##0
                               ( A[W-1]^B[W-1] && (C==sum[W-1]) ));

  // Zero result case
  cv_zero:     cover property (@(A or B) !$isunknown({A,B}) ##0 (sum== '0));

  // Edge cases
  cv_max_plus1: cover property (@(A or B) !$isunknown({A,B}) ##0 (A==MAX && B==1));
  cv_min_minus1:cover property (@(A or B) !$isunknown({A,B}) ##0 (A==MIN && B==-1));

endmodule

// Example bind (uncomment in your TB or a bind file):
// bind adder adder_sva #(8) sva_i (.*);
// SVA for signed_mag_comp
// Binds into the DUT; checks abs/sign/mag/compare and provides focused coverage.

checker signed_mag_comp_chk (
  input logic                 clk,
  input logic signed [3:0]    A,
  input logic signed [3:0]    B,
  input logic                 C,
  input logic        [3:0]    A_abs_reg,
  input logic        [3:0]    B_abs_reg,
  input logic        [3:0]    A_sign_reg,
  input logic        [3:0]    B_sign_reg,
  input logic        [3:0]    A_mag_reg,
  input logic        [3:0]    B_mag_reg
);
  default clocking @(posedge clk); endclocking

  function automatic logic [3:0] abs4 (input logic signed [3:0] x);
    abs4 = x[3] ? (~x + 4'd1) : x;
  endfunction

  // Known-value gating
  property p_known_in; !$isunknown({A,B}); endproperty

  // X/Z checks
  assert property (p_known_in |-> !$isunknown(C));
  assert property (p_known_in |-> !$isunknown({A_abs_reg,B_abs_reg,A_sign_reg,B_sign_reg,A_mag_reg,B_mag_reg}));

  // Stage 1: absolute value
  assert property (p_known_in |-> A_abs_reg == abs4(A));
  assert property (p_known_in |-> B_abs_reg == abs4(B));

  // Stage 2: sign extraction (note: A_sign_reg/B_sign_reg are 4b with only bit0 used)
  assert property (A_sign_reg == {3'b000, A[3]});
  assert property (B_sign_reg == {3'b000, B[3]});

  // Stage 3: max/min permutation and ordering
  assert property (A_mag_reg >= B_mag_reg);
  assert property ((A_mag_reg == A_abs_reg && B_mag_reg == B_abs_reg) ||
                   (A_mag_reg == B_abs_reg && B_mag_reg == A_abs_reg));

  // Stage 4: registered compare equals combinational compare
  assert property (C == (A_mag_reg >= B_mag_reg));

  // Spec from inputs (sanity: ties C to input-only function)
  assert property (C == (abs4(A) >= abs4(B)));

  // Targeted coverage
  cover property (abs4(A) >  abs4(B) && C);
  cover property (abs4(A) == abs4(B) && C);
  cover property (abs4(A) <  abs4(B) && C);

  cover property ( A[3] && !B[3]);  // A negative, B non-negative
  cover property (!A[3] &&  B[3]);  // A non-negative, B negative
  cover property ( A[3] &&  B[3]);  // both negative
  cover property (!A[3] && !B[3]);  // both non-negative

  // Edge cases
  cover property (A == 4'sd-8);
  cover property (B == 4'sd-8);
  cover property (A == 4'sd0);
  cover property (B == 4'sd0);
  cover property (A == 4'sd7);
  cover property (B == 4'sd-7);

  // Negative cover: C==0 is expected unreachable with current RTL
  cover property (C == 1'b0);
endchecker

bind signed_mag_comp signed_mag_comp_chk i_signed_mag_comp_chk (
  .clk       (clk),
  .A         (A),
  .B         (B),
  .C         (C),
  .A_abs_reg (A_abs_reg),
  .B_abs_reg (B_abs_reg),
  .A_sign_reg(A_sign_reg),
  .B_sign_reg(B_sign_reg),
  .A_mag_reg (A_mag_reg),
  .B_mag_reg (B_mag_reg)
);
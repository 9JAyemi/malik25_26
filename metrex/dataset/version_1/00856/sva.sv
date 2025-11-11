// SVA for ripple_carry_adder
module rca4_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout
);

  // Local ripple relations
  let c1 = (A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin);
  let s0 = A[0] ^ B[0] ^ Cin;

  let c2 = (A[1] & B[1]) | (A[1] & c1)  | (B[1] & c1);
  let s1 = A[1] ^ B[1] ^ c1;

  let c3 = (A[2] & B[2]) | (A[2] & c2)  | (B[2] & c2);
  let s2 = A[2] ^ B[2] ^ c2;

  let c4 = (A[3] & B[3]) | (A[3] & c3)  | (B[3] & c3);
  let s3 = A[3] ^ B[3] ^ c3;

  // Correct 5-bit sum
  property p_sum_correct;
    disable iff ($isunknown({A,B,Cin,S,Cout}))
    {Cout,S} == A + B + Cin;
  endproperty
  assert property (@(A or B or Cin or S or Cout) p_sum_correct);

  // Bitwise ripple relations (redundant to sum, but great debug)
  property p_bitwise_ripple;
    disable iff ($isunknown({A,B,Cin,S,Cout}))
    (S[0] == s0) && (S[1] == s1) && (S[2] == s2) && (S[3] == s3) && (Cout == c4);
  endproperty
  assert property (@(A or B or Cin or S or Cout) p_bitwise_ripple);

  // No X on outputs when inputs known
  property p_no_x_out_when_inputs_known;
    !$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout});
  endproperty
  assert property (@(A or B or Cin or S or Cout) p_no_x_out_when_inputs_known);

  // Outputs only change when inputs change (no spurious glitches)
  property p_outputs_change_implies_inputs_change;
    disable iff ($isunknown({A,B,Cin,S,Cout}))
    $changed({S,Cout}) |-> $changed({A,B,Cin});
  endproperty
  assert property (@(A or B or Cin or S or Cout) p_outputs_change_implies_inputs_change);

  // Coverage
  cover property (@(A or B or Cin or S or Cout)
    ! $isunknown({A,B,Cin,S,Cout}) && (A==4'b0000) && (B==4'b0000) && (Cin==1'b0) && (S==4'b0000) && (Cout==1'b0)); // zero + zero, no carry

  cover property (@(A or B or Cin or S or Cout)
    ! $isunknown({A,B,Cin,S,Cout}) && (A==4'b0000) && (B==4'b0000) && (Cin==1'b1) && (S==4'b0001) && (Cout==1'b0)); // Cin only

  cover property (@(A or B or Cin or S or Cout)
    ! $isunknown({A,B,Cin,S,Cout}) && (A==4'hF) && (B==4'h0) && (Cin==1'b0) && (S==4'hF) && (Cout==1'b0)); // max + 0, no carry

  cover property (@(A or B or Cin or S or Cout)
    ! $isunknown({A,B,Cin,S,Cout}) && (A==4'hF) && (B==4'hF) && (Cin==1'b1) && (Cout==1'b1)); // full overflow

  cover property (@(A or B or Cin or S or Cout)
    ! $isunknown({A,B,Cin,S,Cout}) && (A==4'b1111) && (B==4'b0000) && (Cin==1'b1) && (S==4'b0000) && (Cout==1'b1)); // full propagate chain

  cover property (@(A or B or Cin or S or Cout)
    ! $isunknown({A,B,Cin,S,Cout}) && (A[0]&B[0]) && !Cin && (S[0]==1'b0) && (c1==1'b1)); // generate at bit0

  cover property (@(A or B or Cin or S or Cout)
    ! $isunknown({A,B,Cin,S,Cout}) && (A[0]^B[0]) && Cin && (S[0]==1'b0) && (c1==1'b1));  // propagate at bit0

endmodule

// Bind into DUT
bind ripple_carry_adder rca4_sva rca4_sva_i (.*);
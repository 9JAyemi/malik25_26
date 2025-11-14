// SVA for add4bit
module add4bit_sva(
  input logic [3:0] A, B,
  input logic [4:0] SUM
);
  // Helpers
  let exp_sum      = ({1'b0, A} + {1'b0, B});
  let known_inputs = !$isunknown({A,B});

  // Functional correctness (sample after delta to avoid races)
  property p_sum_correct;
    @(A or B) disable iff (!known_inputs)
      1'b1 |-> ##0 (SUM == exp_sum);
  endproperty
  assert property (p_sum_correct);

  // No X/Z on SUM when inputs are known
  property p_sum_known;
    @(A or B) known_inputs |-> ##0 !$isunknown(SUM);
  endproperty
  assert property (p_sum_known);

  // Carry bit correctness
  property p_carry_correct;
    @(A or B) disable iff (!known_inputs)
      ##0 (SUM[4] == exp_sum[4]);
  endproperty
  assert property (p_carry_correct);

  // SUM should never be 31 (max legal is 30)
  property p_no_31;
    @(A or B) disable iff (!known_inputs)
      ##0 (SUM != 5'd31);
  endproperty
  assert property (p_no_31);

  // Coverage: no-carry, carry, and key corner/boundary cases
  cover property (@(A or B) known_inputs ##0 (exp_sum <  5'd16));
  cover property (@(A or B) known_inputs ##0 (exp_sum >= 5'd16));
  cover property (@(A or B) known_inputs ##0 (A==4'd0  && B==4'd0  && SUM==5'd0));
  cover property (@(A or B) known_inputs ##0 (A==4'd15 && B==4'd0  && SUM==5'd15));
  cover property (@(A or B) known_inputs ##0 (A==4'd15 && B==4'd1  && SUM==5'd16));
  cover property (@(A or B) known_inputs ##0 (A==4'd8  && B==4'd8  && SUM==5'd16));
  cover property (@(A or B) known_inputs ##0 (A==4'd15 && B==4'd15 && SUM==5'd30));
endmodule

bind add4bit add4bit_sva sva_i(.A(A), .B(B), .SUM(SUM));
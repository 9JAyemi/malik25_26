// SVA checker and bind for binary_adder
module binary_adder_sva (input logic [3:0] A, B, input logic [3:0] S);

  // 5-bit sum for precise carry detection
  let sum5 = ({1'b0, A} + {1'b0, B});

  // Output must be known when inputs are known
  property p_known_out;
    @(A or B or S) (!$isunknown({A,B})) |-> ##0 !$isunknown(S);
  endproperty
  assert property (p_known_out);

  // Functional correctness: S = (A+B) mod 16
  property p_mod16_correct;
    @(A or B) (!$isunknown({A,B})) |-> ##0 (S === sum5[3:0]);
  endproperty
  assert property (p_mod16_correct);

  // No spurious output change without an input change
  property p_no_spurious_change;
    @(A or B or S) $changed(S) |-> ($changed(A) || $changed(B));
  endproperty
  assert property (p_no_spurious_change);

  // Coverage: both carry and no-carry cases
  cover property (@(A or B) (!$isunknown({A,B})) && !sum5[4] ##0 (S === sum5[3:0]));
  cover property (@(A or B) (!$isunknown({A,B})) &&  sum5[4] ##0 (S === sum5[3:0]));

  // Boundary/corner cases
  cover property (@(A or B) A==4'h0 && B==4'h0 ##0 S==4'h0);
  cover property (@(A or B) A==4'hF && B==4'h0 ##0 S==4'hF);
  cover property (@(A or B) A==4'hF && B==4'h1 ##0 S==4'h0);
  cover property (@(A or B) A==4'h8 && B==4'h8 ##0 S==4'h0);

endmodule

bind binary_adder binary_adder_sva i_binary_adder_sva (.*);
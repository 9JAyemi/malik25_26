// SVA for four_bit_comparator (bindable, clockless, race-safe with ##0)
module four_bit_comparator_sva (input [3:0] A, input [3:0] B, input out);

  // Functional correctness: out equals (A > B) after combinational settle
  property p_cmp_correct;
    @(A or B) 1'b1 |-> ##0 (out == (A > B));
  endproperty
  a_cmp_correct: assert property (p_cmp_correct);

  // Output must always be known (no X/Z)
  a_out_known: assert property (@(A or B or out) 1'b1 |-> ##0 !$isunknown(out));

  // Out can change only when inputs change (no spontaneous glitches)
  property p_out_only_if_inputs_change;
    @(out) 1'b1 |-> ($changed(A) || $changed(B));
  endproperty
  a_out_only_if_inputs_change: assert property (p_out_only_if_inputs_change);

  // Functional coverage: all compare relations
  c_gt: cover property (@(A or B) (A > B));
  c_lt: cover property (@(A or B) (A < B));
  c_eq: cover property (@(A or B) (A == B));

  // Boundary coverage
  c_minmax1: cover property (@(A or B) (A==4'd0  && B==4'd15));
  c_minmax2: cover property (@(A or B) (A==4'd15 && B==4'd0));

  // Output toggle coverage
  c_out_rise: cover property (@(out) $rose(out));
  c_out_fall: cover property (@(out) $fell(out));

endmodule

// Bind into DUT
bind four_bit_comparator four_bit_comparator_sva sva_i(.A(A), .B(B), .out(out));
// SVA checker for four_input_one_output
module four_input_one_output_sva (input logic a, b, c, d, input logic out);
  logic [3:0] in;  assign in = {a,b,c,d};
  logic       or_in; assign or_in = |in;

  // Functional equivalence when inputs are known; check after comb settles
  property p_or_equiv_known;
    @(a or b or c or d) !$isunknown(in) |-> ##0 (! $isunknown(out) && out == or_in);
  endproperty
  a_or_equiv_known: assert property (p_or_equiv_known);

  // Output may only change due to a change in the OR of inputs, and must match it
  property p_out_change_caused_by_in_change;
    @(out) 1 |-> ##0 ($changed(or_in) && ! $isunknown(or_in) && out == or_in);
  endproperty
  a_out_change_caused_by_in_change: assert property (p_out_change_caused_by_in_change);

  // Coverage: key cases
  c_all_zero:   cover property (@(a or b or c or d) !$isunknown(in) && in == 4'b0000 && out == 1'b0);
  c_only_a:     cover property (@(a or b or c or d) !$isunknown(in) && in == 4'b1000 && out == 1'b1);
  c_only_b:     cover property (@(a or b or c or d) !$isunknown(in) && in == 4'b0100 && out == 1'b1);
  c_only_c:     cover property (@(a or b or c or d) !$isunknown(in) && in == 4'b0010 && out == 1'b1);
  c_only_d:     cover property (@(a or b or c or d) !$isunknown(in) && in == 4'b0001 && out == 1'b1);
  c_two_ones:   cover property (@(a or b or c or d) !$isunknown(in) && $countones(in) == 2 && out == 1'b1);
  c_three_ones: cover property (@(a or b or c or d) !$isunknown(in) && $countones(in) == 3 && out == 1'b1);
  c_all_ones:   cover property (@(a or b or c or d) !$isunknown(in) && in == 4'b1111 && out == 1'b1);
  c_input_x:    cover property (@(a or b or c or d) $isunknown(in));
endmodule

bind four_input_one_output four_input_one_output_sva sva (.a(a), .b(b), .c(c), .d(d), .out(out));
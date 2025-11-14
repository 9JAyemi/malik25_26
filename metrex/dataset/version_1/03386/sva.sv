// SVA checker for Select_AB
module Select_AB_sva (
  input logic in_select,
  input logic in1,
  input logic in2,
  input logic A,
  input logic B
);

  // Functional equivalence (both outputs) when all controls/data are known
  property p_mux_function;
    @(in_select or in1 or in2 or A or B)
    disable iff ($isunknown({in_select,in1,in2}))
      (A == (in_select ? in1 : in2)) &&
      (B == (in_select ? in2 : in1));
  endproperty
  ap_mux_function: assert property (p_mux_function) else
    $error("Select_AB: mux mapping failed (known select/data)");

  // Edge-based sanity on select transitions (inputs known)
  property p_sel1_mapping;
    @(posedge in_select)
    disable iff ($isunknown({in1,in2}))
      (A == in1) && (B == in2);
  endproperty
  ap_sel1_mapping: assert property (p_sel1_mapping) else
    $error("Select_AB: posedge select mapping failed");

  property p_sel0_mapping;
    @(negedge in_select)
    disable iff ($isunknown({in1,in2}))
      (A == in2) && (B == in1);
  endproperty
  ap_sel0_mapping: assert property (p_sel0_mapping) else
    $error("Select_AB: negedge select mapping failed");

  // X-propagation: unknown select with equal known inputs must pass the value through
  property p_x_selX_equal_inputs;
    @(in_select or in1 or in2 or A or B)
      ($isunknown(in_select) && !$isunknown({in1,in2}) && (in1 === in2))
      |-> ##0 (A === in1) && (B === in1);
  endproperty
  ap_x_selX_equal_inputs: assert property (p_x_selX_equal_inputs) else
    $error("Select_AB: X-select with equal inputs did not pass value");

  // X-propagation: unknown select with different known inputs must yield X on both outputs
  property p_x_selX_diff_inputs;
    @(in_select or in1 or in2 or A or B)
      ($isunknown(in_select) && !$isunknown({in1,in2}) && (in1 !== in2))
      |-> ##0 ($isunknown(A) && $isunknown(B));
  endproperty
  ap_x_selX_diff_inputs: assert property (p_x_selX_diff_inputs) else
    $error("Select_AB: X-select with different inputs did not drive X on both outputs");

  // Outputs equality reflects inputs equality when data known (independent of select)
  property p_eq_reflection;
    @(in_select or in1 or in2 or A or B)
    disable iff ($isunknown({in1,in2}))
      ((in1 === in2) |-> ##0 (A === B)) and
      ((in1 !== in2) |-> ##0 (A !== B));
  endproperty
  ap_eq_reflection: assert property (p_eq_reflection) else
    $error("Select_AB: outputs equality/inequality does not reflect inputs");

  // Functional coverage
  // Cover both select settings with equal/different inputs
  cp_sel0_eq:   cover property (@(in_select or in1 or in2) (! $isunknown({in1,in2})) && (in_select==1'b0) && (in1===in2) && (A==in2) && (B==in1));
  cp_sel0_diff: cover property (@(in_select or in1 or in2) (! $isunknown({in1,in2})) && (in_select==1'b0) && (in1!==in2) && (A==in2) && (B==in1));
  cp_sel1_eq:   cover property (@(in_select or in1 or in2) (! $isunknown({in1,in2})) && (in_select==1'b1) && (in1===in2) && (A==in1) && (B==in2));
  cp_sel1_diff: cover property (@(in_select or in1 or in2) (! $isunknown({in1,in2})) && (in_select==1'b1) && (in1!==in2) && (A==in1) && (B==in2));

  // Cover select edges
  cp_posedge_sel: cover property (@(posedge in_select) (! $isunknown({in1,in2})) && (A==in1) && (B==in2));
  cp_negedge_sel: cover property (@(negedge in_select) (! $isunknown({in1,in2})) && (A==in2) && (B==in1));

  // Cover X-select behavior (equal and different inputs)
  cp_x_sel_eq:   cover property (@(in_select or in1 or in2) ($isunknown(in_select) && !$isunknown({in1,in2}) && (in1===in2) && (A===in1) && (B===in1)));
  cp_x_sel_diff: cover property (@(in_select or in1 or in2) ($isunknown(in_select) && !$isunknown({in1,in2}) && (in1!==in2) && $isunknown(A) && $isunknown(B)));

endmodule

// Bind into DUT
bind Select_AB Select_AB_sva sva_i (
  .in_select(in_select),
  .in1(in1),
  .in2(in2),
  .A(A),
  .B(B)
);
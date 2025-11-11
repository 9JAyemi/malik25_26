// SVA checker for mux2to1. Bind this to the DUT.
module mux2to1_sva(
  input logic [3:0] in0, in1,
  input logic       sel,
  input logic [3:0] out
);

  // Core functional equivalence (4-state accurate, same time slot)
  property p_mux_func;
    @(in0 or in1 or sel or out) ##0 (out === (sel ? in1 : in0));
  endproperty
  assert property (p_mux_func);

  // If all inputs are known, output must be known and equal (2-state compare)
  property p_no_x_when_inputs_known;
    @(in0 or in1 or sel or out)
      (!$isunknown({in0,in1,sel})) |-> ##0 (! $isunknown(out) && (out == (sel ? in1 : in0)));
  endproperty
  assert property (p_no_x_when_inputs_known);

  // With unknown sel, equal data on both inputs must pass through
  property p_merge_when_sel_x_and_data_equal;
    @(in0 or in1 or sel or out)
      ($isunknown(sel) && (in0 === in1)) |-> ##0 (out === in0);
  endproperty
  assert property (p_merge_when_sel_x_and_data_equal);

  // Branch-specific clarity (useful localized failures)
  assert property (@(in0 or sel or out) (sel === 1'b0) |-> ##0 (out === in0));
  assert property (@(in1 or sel or out) (sel === 1'b1) |-> ##0 (out === in1));

  // Coverage: exercise both selects, differing/equal data, and sel toggles with stable data
  cover property (@(in0 or in1 or sel) (sel === 1'b0));
  cover property (@(in0 or in1 or sel) (sel === 1'b1));
  cover property (@(in0 or in1 or sel) (in0 != in1) && (sel === 1'b0) ##0 (out == in0));
  cover property (@(in0 or in1 or sel) (in0 != in1) && (sel === 1'b1) ##0 (out == in1));
  cover property (@(in0 or in1 or sel) (in0 === in1) && $isunknown(sel) ##0 (out === in0));
  cover property (@(in0 or in1 or sel) $changed(sel) && $stable(in0) && $stable(in1) ##0 (out === (sel ? in1 : in0)));

endmodule

bind mux2to1 mux2to1_sva (.in0(in0), .in1(in1), .sel(sel), .out(out));
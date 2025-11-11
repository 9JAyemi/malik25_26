// SVA checker for mux_2_to_1_en
module mux_2_to_1_en_sva(
  input logic a,
  input logic b,
  input logic en,
  input logic out
);

  // Sample on any design activity (combinational)
  default clocking cb @(*) endclocking

  // Functional equivalence to ternary operator (4-state accurate)
  a_func:           assert property (out === (en ? b : a));

  // Simple select-path checks
  a_sel0:           assert property ((en === 1'b0) |-> (out === a));
  a_sel1:           assert property ((en === 1'b1) |-> (out === b));

  // When inputs equal, output must equal that value regardless of en/X
  a_equal_inputs:   assert property ((a === b) |-> (out === a));

  // Known-propagation: all-known inputs imply known output
  a_no_x_from_known:assert property ((!$isunknown({en,a,b})) |-> (!$isunknown(out)));

  // Enable edge behavior (combinational response)
  a_rose_en:        assert property ($rose(en) |-> (out === b));
  a_fell_en:        assert property ($fell(en) |-> (out === a));

  // No spurious output changes without input changes
  a_stable:         assert property ($stable({en,a,b}) |-> $stable(out));

  // X-propagation characteristics of ?: operator
  a_xprop_diff:     assert property (($isunknown(en) && (a !== b)) |-> $isunknown(out));
  a_xprop_same:     assert property (($isunknown(en) && (a === b)) |-> (out === a));

  // Coverage: exercise both paths, toggles, and X behavior
  c_sel0:           cover  property ((en === 1'b0) && (out === a));
  c_sel1:           cover  property ((en === 1'b1) && (out === b));
  c_en_toggle_up:   cover  property ($rose(en));
  c_en_toggle_down: cover  property ($fell(en));
  c_x_en_diff:      cover  property ($isunknown(en) && (a !== b) && $isunknown(out));

endmodule

// Bind into the DUT
bind mux_2_to_1_en mux_2_to_1_en_sva u_mux_2_to_1_en_sva(
  .a(a), .b(b), .en(en), .out(out)
);
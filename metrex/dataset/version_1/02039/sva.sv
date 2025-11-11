// SVA for mux_2to1_behavioral
module mux_2to1_sva #(parameter WIDTH=4)(
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  input  logic             s,
  input  logic [WIDTH-1:0] mux_out
);

  // Functional correctness (sample after delta on any input/change)
  property p_func;
    @(a or b or s) 1 |-> ##0 (mux_out == (s ? b : a));
  endproperty
  assert property (p_func)
    else $error("MUX functional mismatch: mux_out != (s ? b : a)");

  // No spurious output toggles without a,b,s changing
  property p_no_spurious_toggle;
    @(a or b or s or mux_out) $changed(mux_out) |-> (!$stable(a) || !$stable(b) || !$stable(s));
  endproperty
  assert property (p_no_spurious_toggle)
    else $error("mux_out changed while a,b,s were stable");

  // Select toggle effects with stable data
  property p_sel_toggle_changes_when_data_diff;
    @(s or a or b)
      ($changed(s) && $stable(a) && $stable(b) && (a != b)) |-> ##0 $changed(mux_out);
  endproperty
  assert property (p_sel_toggle_changes_when_data_diff)
    else $error("mux_out did not change when s toggled and a!=b");

  property p_sel_toggle_nochange_when_data_equal;
    @(s or a or b)
      ($changed(s) && $stable(a) && $stable(b) && (a == b)) |-> ##0 !$changed(mux_out);
  endproperty
  assert property (p_sel_toggle_nochange_when_data_equal)
    else $error("mux_out changed when s toggled and a==b");

  // X-propagation checks on selected path
  property p_known_out_when_s0_a_known;
    @(a or b or s) (s === 1'b0 && !$isunknown(a)) |-> ##0 (!$isunknown(mux_out) && mux_out == a);
  endproperty
  assert property (p_known_out_when_s0_a_known)
    else $error("Unknown/wrong mux_out when s=0 and a is known");

  property p_known_out_when_s1_b_known;
    @(a or b or s) (s === 1'b1 && !$isunknown(b)) |-> ##0 (!$isunknown(mux_out) && mux_out == b);
  endproperty
  assert property (p_known_out_when_s1_b_known)
    else $error("Unknown/wrong mux_out when s=1 and b is known");

  // Targeted functional coverage
  cover property (@(a or b or s) (s === 1'b0 && a != b) ##0 (mux_out == a));
  cover property (@(a or b or s) (s === 1'b1 && a != b) ##0 (mux_out == b));
  cover property (@(s) $rose(s) && $stable(a) && $stable(b) && (a != b) ##0 (mux_out == b));
  cover property (@(s) $fell(s) && $stable(a) && $stable(b) && (a != b) ##0 (mux_out == a));
  cover property (@(s) $changed(s) && $stable(a) && $stable(b) && (a == b) ##0 !$changed(mux_out));

endmodule

bind mux_2to1_behavioral mux_2to1_sva #(.WIDTH(4)) mux_2to1_sva_i (
  .a(a), .b(b), .s(s), .mux_out(mux_out)
);
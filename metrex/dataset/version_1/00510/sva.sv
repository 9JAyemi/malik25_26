// SVA for mux_2_1
module mux_2_1_sva(
  input logic a,
  input logic b,
  input logic en,
  input logic y
);
  // Functional correctness after NBA in same timestep
  property p_func_correct;
    @(a or b or en) 1'b1 |-> ##0 (y === (en ? b : a));
  endproperty
  assert property (p_func_correct);

  // No X/Z on y when inputs are known
  property p_no_x_when_inputs_known;
    @(a or b or en or y) (!$isunknown({a,b,en})) |-> ##0 !$isunknown(y);
  endproperty
  assert property (p_no_x_when_inputs_known);

  // Unselected input must not affect y
  property p_b_ignored_when_en0;
    @(b or en or a) (en==1'b0 && $changed(b) && $stable(en) && $stable(a)) |-> ##0 $stable(y);
  endproperty
  assert property (p_b_ignored_when_en0);

  property p_a_ignored_when_en1;
    @(a or en or b) (en==1'b1 && $changed(a) && $stable(en) && $stable(b)) |-> ##0 $stable(y);
  endproperty
  assert property (p_a_ignored_when_en1);

  // Toggling en when a==b must not change y
  property p_en_toggle_no_effect_when_inputs_equal;
    @(en or a or b) ($changed(en) && (a === b)) |-> ##0 $stable(y);
  endproperty
  assert property (p_en_toggle_no_effect_when_inputs_equal);

  // Coverage: both paths and values
  cover property (@(a or en) (en==0 && a==0) ##0 (y==0));
  cover property (@(a or en) (en==0 && a==1) ##0 (y==1));
  cover property (@(b or en) (en==1 && b==0) ##0 (y==0));
  cover property (@(b or en) (en==1 && b==1) ##0 (y==1));

  // Coverage: select changes with differing inputs
  cover property (@(en or a or b) $rose(en) && (a !== b) ##0 (y === b));
  cover property (@(en or a or b) $fell(en) && (a !== b) ##0 (y === a));

  // Coverage: data changes propagate on selected path
  cover property (@(b or en) (en && $changed(b)) ##0 $changed(y));
  cover property (@(a or en) (!en && $changed(a)) ##0 $changed(y));

  // Coverage: en toggle when inputs equal
  cover property (@(en or a or b) (a === b) && $changed(en));
endmodule

bind mux_2_1 mux_2_1_sva sva_mux(.a(a), .b(b), .en(en), .y(y));
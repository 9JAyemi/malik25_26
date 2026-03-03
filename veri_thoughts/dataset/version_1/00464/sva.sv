// SVA checker for mux_4to1. Bind this to the DUT.
module mux_4to1_sva (
  input logic in0,
  input logic in1,
  input logic in2,
  input logic in3,
  input logic sel0,
  input logic sel1,
  input logic out
);

  // Functional equivalence (delta-cycle settled)
  // Out must equal the selected input after any input/select change.
  property p_mux_func;
    @(in0 or in1 or in2 or in3 or sel0 or sel1)
      1'b1 |-> ##0 (out === (sel1 ? (sel0 ? in3 : in2) : (sel0 ? in1 : in0)));
  endproperty
  assert property (p_mux_func);

  // No X on out when select and selected input are known
  property p_no_x_when_known;
    @(in0 or in1 or in2 or in3 or sel0 or sel1)
      (!$isunknown({sel1,sel0}) &&
       !$isunknown( sel1 ? (sel0 ? in3 : in2) : (sel0 ? in1 : in0) ))
      |-> ##0 (! $isunknown(out) &&
               out == (sel1 ? (sel0 ? in3 : in2) : (sel0 ? in1 : in0)));
  endproperty
  assert property (p_no_x_when_known);

  // Insensitivity to unselected inputs (no unintended influence)
  // If only unselected inputs change and select+selected input are stable, out must stay stable.

  // sel = 00, selected in0
  property p_unselected_00_stable;
    @(in0 or in1 or in2 or in3 or sel0 or sel1)
      (!$isunknown({sel1,sel0}) && {sel1,sel0}==2'b00 &&
       $stable({sel1,sel0}) && $stable(in0) &&
       ($changed(in1) || $changed(in2) || $changed(in3)))
      |-> ##0 $stable(out);
  endproperty
  assert property (p_unselected_00_stable);

  // sel = 01, selected in1
  property p_unselected_01_stable;
    @(in0 or in1 or in2 or in3 or sel0 or sel1)
      (!$isunknown({sel1,sel0}) && {sel1,sel0}==2'b01 &&
       $stable({sel1,sel0}) && $stable(in1) &&
       ($changed(in0) || $changed(in2) || $changed(in3)))
      |-> ##0 $stable(out);
  endproperty
  assert property (p_unselected_01_stable);

  // sel = 10, selected in2
  property p_unselected_10_stable;
    @(in0 or in1 or in2 or in3 or sel0 or sel1)
      (!$isunknown({sel1,sel0}) && {sel1,sel0}==2'b10 &&
       $stable({sel1,sel0}) && $stable(in2) &&
       ($changed(in0) || $changed(in1) || $changed(in3)))
      |-> ##0 $stable(out);
  endproperty
  assert property (p_unselected_10_stable);

  // sel = 11, selected in3
  property p_unselected_11_stable;
    @(in0 or in1 or in2 or in3 or sel0 or sel1)
      (!$isunknown({sel1,sel0}) && {sel1,sel0}==2'b11 &&
       $stable({sel1,sel0}) && $stable(in3) &&
       ($changed(in0) || $changed(in1) || $changed(in2)))
      |-> ##0 $stable(out);
  endproperty
  assert property (p_unselected_11_stable);

  // Functional coverage

  // Cover all select combinations
  cover property (@(sel0 or sel1) ##0 ({sel1,sel0}==2'b00));
  cover property (@(sel0 or sel1) ##0 ({sel1,sel0}==2'b01));
  cover property (@(sel0 or sel1) ##0 ({sel1,sel0}==2'b10));
  cover property (@(sel0 or sel1) ##0 ({sel1,sel0}==2'b11));

  // Cover pass-through behavior when selected input toggles with stable select
  cover property (@(in0 or sel0 or sel1)
                  ({sel1,sel0}==2'b00 && $stable({sel1,sel0}) && $changed(in0) &&
                   $stable(in1) && $stable(in2) && $stable(in3)) ##0 (out==in0));
  cover property (@(in1 or sel0 or sel1)
                  ({sel1,sel0}==2'b01 && $stable({sel1,sel0}) && $changed(in1) &&
                   $stable(in0) && $stable(in2) && $stable(in3)) ##0 (out==in1));
  cover property (@(in2 or sel0 or sel1)
                  ({sel1,sel0}==2'b10 && $stable({sel1,sel0}) && $changed(in2) &&
                   $stable(in0) && $stable(in1) && $stable(in3)) ##0 (out==in2));
  cover property (@(in3 or sel0 or sel1)
                  ({sel1,sel0}==2'b11 && $stable({sel1,sel0}) && $changed(in3) &&
                   $stable(in0) && $stable(in1) && $stable(in2)) ##0 (out==in3));

endmodule

// Bind into the DUT
bind mux_4to1 mux_4to1_sva mux_4to1_sva_i (.*);
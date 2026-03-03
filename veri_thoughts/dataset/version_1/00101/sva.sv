// SVA for MUX4X1
// Focus: functional correctness, X-propagation, and spurious-change checks.
// Uses event-based sampling since DUT is combinational.

module MUX4X1_sva (
  input [3:0] input_signals,
  input [1:0] select_signals,
  input       output_signal
);

  // Sample on any relevant signal change
  default clocking cb @(input_signals or select_signals or output_signal); endclocking

  // Functional correctness when select is known (2-state)
  property p_func_known_sel;
    !$isunknown(select_signals) |-> ##0 (output_signal === input_signals[select_signals]);
  endproperty
  a_func_known_sel: assert property (p_func_known_sel)
    else $error("MUX4X1: output != selected input with known select");

  // X-propagation when select has any X/Z bit
  property p_x_on_unknown_sel;
    $isunknown(select_signals) |-> ##0 $isunknown(output_signal);
  endproperty
  a_x_on_unknown_sel: assert property (p_x_on_unknown_sel)
    else $error("MUX4X1: output not X when select contains X/Z");

  // Output must not change unless select or the selected input changes
  property p_no_spurious_output_change;
    (!$changed(select_signals) && !$changed(input_signals[select_signals]))
      |-> ##0 (output_signal === $past(output_signal));
  endproperty
  a_no_spurious_output_change: assert property (p_no_spurious_output_change)
    else $error("MUX4X1: output changed without select or selected-input change");

  // Any output change must be caused by some input or select change
  property p_change_has_cause;
    $changed(output_signal) |-> ##0
      ($changed(select_signals)
       || $changed(input_signals[0]) || $changed(input_signals[1])
       || $changed(input_signals[2]) || $changed(input_signals[3]));
  endproperty
  a_change_has_cause: assert property (p_change_has_cause)
    else $error("MUX4X1: output changed without any input/select change");

  // Coverage: hit all select values with correct behavior
  c_sel0: cover property ((!$isunknown(select_signals) && select_signals==2'b00)
                           ##0 (output_signal === input_signals[0]));
  c_sel1: cover property ((!$isunknown(select_signals) && select_signals==2'b01)
                           ##0 (output_signal === input_signals[1]));
  c_sel2: cover property ((!$isunknown(select_signals) && select_signals==2'b10)
                           ##0 (output_signal === input_signals[2]));
  c_sel3: cover property ((!$isunknown(select_signals) && select_signals==2'b11)
                           ##0 (output_signal === input_signals[3]));

  // Coverage: unknown select drives unknown output
  c_selx: cover property ($isunknown(select_signals) ##0 $isunknown(output_signal));

  // Coverage: selected input unknown propagates (with known select)
  c_xprop: cover property ((!$isunknown(select_signals) && $isunknown(input_signals[select_signals]))
                           ##0 $isunknown(output_signal));

endmodule

// Bind to DUT
bind MUX4X1 MUX4X1_sva mux4x1_sva_i(.*);
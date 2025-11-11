// SVA for parity_generator
// Bindable, concise, and full functional/propagation checks + essential coverage

module parity_generator_sva (
  input logic [7:0] in,
  input logic       parity
);

  default clocking cb @(in or parity); endclocking

  // Functional correctness for known inputs
  property p_func_known;
    !$isunknown(in) |-> (parity == (^in));
  endproperty
  assert property (p_func_known);

  // X-propagation: any X/Z on input must produce X on parity
  property p_xprop;
    $isunknown(in) |-> $isunknown(parity);
  endproperty
  assert property (p_xprop);

  // No spurious parity change when inputs stable
  property p_no_spurious_change;
    $stable(in) |-> $stable(parity);
  endproperty
  assert property (p_no_spurious_change);

  // Single-bit input toggle must toggle parity
  property p_single_bit_toggle;
    !($isunknown(in) || $isunknown($past(in))) &&
    $onehot(in ^ $past(in)) |-> (parity != $past(parity));
  endproperty
  assert property (p_single_bit_toggle);

  // Even-number-of-bit toggles preserve parity
  property p_even_toggle_preserve;
    !($isunknown(in) || $isunknown($past(in))) &&
    ($countones(in ^ $past(in)) % 2 == 0) && (in != $past(in)) |-> (parity == $past(parity));
  endproperty
  assert property (p_even_toggle_preserve);

  // Coverage: observe both parity values, toggle behavior, and X propagation
  cover property (!$isunknown(in) && (parity == 1'b0));
  cover property (!$isunknown(in) && (parity == 1'b1));
  cover property (!$isunknown(in) && !$isunknown($past(in)) &&
                  $onehot(in ^ $past(in)) && (parity != $past(parity)));
  cover property ($isunknown(in) && $isunknown(parity));

endmodule

bind parity_generator parity_generator_sva sva (.in(in), .parity(parity));
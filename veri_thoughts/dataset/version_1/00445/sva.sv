// SVA for interstage_buffer_if_id
// Focus: 1-cycle transfer, no spurious updates, knownness, and key functional cover

module interstage_buffer_if_id_sva (
  input  logic        clock,
  input  logic [3:0]  if_control_signals,
  input  logic [3:0]  id_control_signals
);

  // 1-cycle registered transfer (and no X leakage when input was known)
  property p_transfer_1cycle;
    @(posedge clock)
      (!$isunknown($past(if_control_signals))) |-> (id_control_signals === $past(if_control_signals));
  endproperty
  a_transfer_1cycle: assert property(p_transfer_1cycle);

  // If input is stable across a cycle, output must be stable across that cycle
  property p_hold_when_input_stable;
    @(posedge clock)
      (!$isunknown(if_control_signals) && !$isunknown($past(if_control_signals)) &&
       (if_control_signals === $past(if_control_signals)))
      |-> (id_control_signals === $past(id_control_signals));
  endproperty
  a_hold_when_input_stable: assert property(p_hold_when_input_stable);

  // Any known input change must cause an output change exactly next cycle
  property p_change_propagates_next;
    @(posedge clock)
      (!$isunknown(if_control_signals) && !$isunknown($past(if_control_signals)) &&
       (if_control_signals !== $past(if_control_signals)))
      |=> $changed(id_control_signals);
  endproperty
  a_change_propagates_next: assert property(p_change_propagates_next);

  // Output must be known when prior input was known
  property p_no_unknown_out_when_prior_in_known;
    @(posedge clock)
      (!$isunknown($past(if_control_signals))) |-> (!$isunknown(id_control_signals));
  endproperty
  a_no_unknown_out_when_prior_in_known: assert property(p_no_unknown_out_when_prior_in_known);

  // Coverage: observe transfer of edge cases and a generic change
  covergroup cg_vals @(posedge clock);
    coverpoint if_control_signals {
      bins zero = {4'h0};
      bins full = {4'hF};
    }
  endgroup
  cg_vals cg_vals_i = new;

  // Cover that 0x0 and 0xF propagate in the next cycle
  c_prop_zero: cover property (@(posedge clock) (if_control_signals == 4'h0) ##1 (id_control_signals == 4'h0));
  c_prop_full: cover property (@(posedge clock) (if_control_signals == 4'hF) ##1 (id_control_signals == 4'hF));

  // Cover at least one arbitrary change and its propagation
  c_change_then_prop: cover property (@(posedge clock)
                                       (!$isunknown(if_control_signals) && !$isunknown($past(if_control_signals)) &&
                                        (if_control_signals !== $past(if_control_signals)))
                                       ##1 (id_control_signals === $past(if_control_signals)));

endmodule

// Bind into the DUT
bind interstage_buffer_if_id interstage_buffer_if_id_sva sva_inst (
  .clock(clock),
  .if_control_signals(if_control_signals),
  .id_control_signals(id_control_signals)
);
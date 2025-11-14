// SVA for jt51_lfo_lfsr
// Bind to DUT and check reset, shift behavior, tap XOR, stability, and X-propagation.

`ifndef SYNTHESIS
module jt51_lfo_lfsr_sva #(parameter init=220)
(
  input  rst,
  input  clk,
  input  base,
  input  out,
  input  [18:0] bb,
  input  last_base
);
  default clocking cb @(posedge clk); endclocking

  // Output mirrors MSB
  a_out_msb: assert property (out == bb[18]);

  // Reset behavior
  a_reset_vals: assert property (rst |-> (bb == init[18:0] && last_base == 1'b0 && out == init[18]));

  // last_base tracks prior base (only when not crossing reset)
  a_last_base_tracks: assert property ((!rst && $past(!rst)) |-> (last_base == $past(base)));

  // Base-change detection equivalence
  a_change_equiv: assert property ((!rst && $past(!rst)) |-> ((last_base != base) == (base ^ $past(base))));

  // Shift and feedback on base change
  a_shift_on_change: assert property
    ((!rst && $past(!rst) && (base ^ $past(base))) |->
      (bb[18:1] == $past(bb[17:0]) &&
       bb[0]    == ^$past({bb[0],bb[1],bb[14],bb[15],bb[17],bb[18]})));

  // Hold when base is unchanged
  a_hold_when_no_change: assert property
    ((!rst && $past(!rst) && !(base ^ $past(base))) |-> (bb == $past(bb)));

  // No X after reset release
  a_no_x: assert property ((!rst && $past(!rst)) |-> !$isunknown({bb,out,last_base}));

  // Coverage
  c_reset:       cover property (rst);
  c_base_rise:   cover property (!rst && $past(!rst) && $rose(base));
  c_base_fall:   cover property (!rst && $past(!rst) && $fell(base));
  c_two_shifts:  cover property ((!rst && $past(!rst) && (base ^ $past(base))) ##1
                                 (!rst && $past(!rst) && (base ^ $past(base))));
  c_out_toggle:  cover property (!rst && $past(!rst) && (out ^ $past(out)));
endmodule

bind jt51_lfo_lfsr jt51_lfo_lfsr_sva #(.init(init)) (.*);
`endif
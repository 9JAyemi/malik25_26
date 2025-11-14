// SVA for reverse_bit_order
// Bind this module to the DUT: bind reverse_bit_order reverse_bit_order_sva sva();

module reverse_bit_order_sva;

  // Access DUT scope signals directly after bind
  // clk, rst, in[7:0], out[7:0], shift_reg[7:0]

  default clocking cb @(posedge clk); endclocking

  // Reset behavior (synchronous)
  a_rst: assert property (rst |-> (shift_reg == 8'h00 && out == 8'h00));

  // No X/Z on state/outputs when out of reset
  a_no_x: assert property (disable iff (rst) (!$isunknown(shift_reg) && !$isunknown(out)));

  // Shift register correctness
  a_sreg_lsb:   assert property (disable iff (rst) shift_reg[0] == in[0]);
  a_sreg_shift: assert property (disable iff (rst) shift_reg[7:1] == $past(shift_reg[6:0]));

  // Output shift correctness
  a_out_lsb:    assert property (disable iff (rst) out[0] == $past(shift_reg[0]));
  a_out_shift:  assert property (disable iff (rst) out[7:1] == $past(out[6:0]));

  // Out equals the last 8 samples of in[0] (MSB oldest -> LSB newest), once 8 clean cycles after reset
  a_out_window: assert property (disable iff (rst)
                                 !rst[*8] |=> out == { $past(in[0],8), $past(in[0],7), $past(in[0],6), $past(in[0],5),
                                                       $past(in[0],4), $past(in[0],3), $past(in[0],2), $past(in[0],1) });

  // Coverage
  c_reset_pulse:  cover property (rst ##1 !rst);
  c_run_8:        cover property (!rst[*8]);
  c_out0_rise:    cover property (disable iff (rst) $rose(out[0]));
  c_out0_fall:    cover property (disable iff (rst) $fell(out[0]));
  c_out7_toggle:  cover property (disable iff (rst) ($rose(out[7]) or $fell(out[7])));
  c_out_window:   cover property (disable iff (rst)
                                  !rst[*8] |=> out == { $past(in[0],8), $past(in[0],7), $past(in[0],6), $past(in[0],5),
                                                        $past(in[0],4), $past(in[0],3), $past(in[0],2), $past(in[0],1) });

endmodule
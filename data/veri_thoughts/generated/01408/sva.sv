module shift_register_sva (
  input logic clk,
  input logic reset,       // active-high asynchronous reset
  input logic load,
  input logic [3:0] din,
  input logic [3:0] dout,
  input logic [3:0] shift_reg // internal state from RTL
);

  // dout continuously reflects the internal register.
  check_dout_equals_shift_reg: assert property (
    @(posedge clk) (dout == shift_reg)
  );

  // Asserting reset drives the register to zero by the next clock.
  reset_clears_next_cycle: assert property (
    @(posedge clk) reset |=> (dout == 4'd0)
  );

  // If reset is high in consecutive cycles, dout is zero in the current cycle.
  hold_zero_while_reset: assert property (
    @(posedge clk) (reset && $past(reset)) |-> (dout == 4'd0)
  );

  // On the cycle reset deasserts, dout remains zero (from prior reset).
  deassert_reset_zero_now: assert property (
    @(posedge clk) $fell(reset) |-> (dout == 4'd0)
  );

  // Reset has priority over load.
  reset_overrides_load: assert property (
    @(posedge clk) (reset && load) |=> (dout == 4'd0)
  );

  // With load high (and no reset), next-cycle dout equals current din.
  load_captures_din_next: assert property (
    @(posedge clk) disable iff (reset) load |=> (dout == $past(din))
  );

  // With load low (and no reset), next-cycle dout is a left rotate by 1.
  rotate_vector_when_no_load: assert property (
    @(posedge clk) disable iff (reset) (!load) |=> (dout == { $past(dout[2:0]), $past(dout[3]) })
  );

  // Bit mapping of the rotate: next dout[3] comes from previous dout[2].
  rotate_bit3_from_prev_bit2: assert property (
    @(posedge clk) disable iff (reset) (!load) |=> (dout[3] == $past(dout[2]))
  );

  // Bit mapping of the rotate: next dout[2] comes from previous dout[1].
  rotate_bit2_from_prev_bit1: assert property (
    @(posedge clk) disable iff (reset) (!load) |=> (dout[2] == $past(dout[1]))
  );

  // Bit mapping of the rotate: next dout[1] comes from previous dout[0].
  rotate_bit1_from_prev_bit0: assert property (
    @(posedge clk) disable iff (reset) (!load) |=> (dout[1] == $past(dout[0]))
  );

  // Bit mapping of the rotate: next dout[0] comes from previous dout[3].
  rotate_bit0_from_prev_bit3: assert property (
    @(posedge clk) disable iff (reset) (!load) |=> (dout[0] == $past(dout[3]))
  );

  // Four consecutive rotates (no loads) return to the original value.
  four_rotations_return_to_original: assert property (
    @(posedge clk) disable iff (reset) (!load)[*4] |=> (dout == $past(dout,4))
  );

endmodule
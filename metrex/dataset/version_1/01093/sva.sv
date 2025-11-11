// SVA for shift_register_d_ff
// Notes:
// - d is unused in DUT.
// - shift_register_out is 3 bits but driven by 1 bit; below assertions check the actual behavior:
//   shift_register_out[2:1]==0 and shift_register_out[0]==shift_register[2].

module shift_register_d_ff_sva (shift_register_d_ff dut);

  // establish valid $past()
  bit past_valid;
  initial past_valid = 0;
  always @(posedge dut.clk) past_valid <= 1;

  // Next-state functional relation of internal state
  property p_next_state;
    @(posedge dut.clk)
      disable iff (!past_valid || $isunknown($past(dut.shift_register)))
      dut.shift_register ==
        { $past(dut.shift_register[1]),
          $past(dut.shift_register[2]),
          $past(dut.shift_register[0]) ^ $past(dut.shift_register[2]) };
  endproperty
  assert property (p_next_state);

  // Output mapping must reflect internal state (checks width-mismatch consequence)
  assert property (@(posedge dut.clk)
                   dut.q == dut.shift_register[0]);

  assert property (@(posedge dut.clk)
                   dut.shift_register_out == {2'b00, dut.shift_register[2]});

  // Sanity: outputs are never X/Z when internal state is known
  assert property (@(posedge dut.clk)
                   !$isunknown(dut.shift_register) |-> (!$isunknown(dut.q) && !$isunknown(dut.shift_register_out)));

  // Coverage
  cover property (@(posedge dut.clk) past_valid ##1 $changed(dut.shift_register));     // state changes
  cover property (@(posedge dut.clk) $changed(dut.q));                                  // q toggles
  cover property (@(posedge dut.clk) $changed(dut.shift_register_out[0]));              // visible output LSB toggles

  // Optional: hit all 3-bit states (if reachable based on initial conditions)
  cover property (@(posedge dut.clk) dut.shift_register == 3'b000);
  cover property (@(posedge dut.clk) dut.shift_register == 3'b001);
  cover property (@(posedge dut.clk) dut.shift_register == 3'b010);
  cover property (@(posedge dut.clk) dut.shift_register == 3'b011);
  cover property (@(posedge dut.clk) dut.shift_register == 3'b100);
  cover property (@(posedge dut.clk) dut.shift_register == 3'b101);
  cover property (@(posedge dut.clk) dut.shift_register == 3'b110);
  cover property (@(posedge dut.clk) dut.shift_register == 3'b111);

endmodule

// Bind into DUT
bind shift_register_d_ff shift_register_d_ff_sva u_shift_register_d_ff_sva();
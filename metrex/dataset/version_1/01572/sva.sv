// SystemVerilog Assertions for encryption_module
// Bind into DUT to access internals
bind encryption_module encryption_module_sva();

module encryption_module_sva;

  // Use DUT scope signals directly (via bind)
  // clk, rst, in, key, out, shift_reg, shift_reg_out, barrel_shifter_out, xor_out

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior
  a_reset_scalar: assert property (rst |-> (shift_reg_out==5'd0 && barrel_shifter_out==100'b0 && xor_out==100'b0 && out==100'b0));
  a_reset_array:  assert property (rst |-> (foreach (shift_reg[i]) (shift_reg[i]==5'd0)));

  // Shift chain correctness (avoids shift_reg[0] race)
  genvar j;
  for (j=1; j<100; j++) begin : g_shift
    a_shift_chain: assert property (shift_reg[j] == $past(shift_reg[j-1]));
  end
  a_tap_delay: assert property (shift_reg_out == $past(shift_reg[4]));

  // Data constraints implied by design: shift_reg only ever holds 0/1
  a_shift_bits_binary: assert property (foreach (shift_reg[i]) (shift_reg[i] inside {5'd0,5'd1}));
  a_tap_binary:        assert property (shift_reg_out inside {5'd0,5'd1});

  // Barrel shifter behavior
  // Given shift_reg_out is 0 or 1 (from above), DUT should effectively pass input through
  a_barrel_passthru: assert property (barrel_shifter_out == in);

  // XOR behavior and width-mismatch consequences (key zero-extends to 100 bits)
  a_xor_upper_passthru: assert property (xor_out[99:32] == barrel_shifter_out[99:32]);
  a_xor_lower_xor:      assert property (xor_out[31:0]  == (barrel_shifter_out[31:0] ^ key));
  a_key_zero_passthru:  assert property (key==32'd0 |-> xor_out == barrel_shifter_out);

  // Output assignment
  a_out_matches_reg: assert property (out == xor_out);

  // No X/Z on critical outputs after reset released
  a_no_unknowns: assert property (!$isunknown({shift_reg_out, barrel_shifter_out, xor_out, out})));

  // Functional coverage
  // 1) Exercise both tap values (0 and 1), and observe barrel_shifter_out pass-through
  c_tap0: cover property (shift_reg_out==5'd0 && barrel_shifter_out==in);
  c_tap1: cover property ($rose(in[99]) ##5 (shift_reg_out==5'd1 && barrel_shifter_out==in));

  // 2) XOR pass-through vs. mixing when key is zero vs. non-zero
  c_key_zero:    cover property (key==32'd0 ##1 (out==in));
  c_key_nonzero: cover property (key!=32'd0 ##1 (out[31:0] == (in[31:0] ^ key)));

endmodule
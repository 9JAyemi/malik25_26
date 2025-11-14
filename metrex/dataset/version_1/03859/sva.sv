// SVA for counter_combination and top_module
// Bind these to the DUTs

// Assertions for counter_combination
module cc_sva;
  default clocking cb @(posedge clk); endclocking

  // Reset clears counter next cycle
  a_cc_reset: assert property (reset |=> count_reg == 4'b0000);

  // Monotonic +1 increment when not in reset
  a_cc_inc:   assert property (disable iff (reset) count_reg == $past(count_reg) + 1);

  // Outputs implement mask function
  a_cc_outv_func: assert property (outv == (count_reg & {vec, 2'b00}));
  a_cc_o1_map:    assert property (o1 == outv[3]);
  a_cc_o0_map:    assert property (o0 == outv[2]);
  a_cc_low_zero:  assert property (outv[1:0] == 2'b00);

  // No X/Z after reset
  a_cc_no_x: assert property (disable iff (reset) !$isunknown({count_reg, outv, o1, o0}));

  // Coverage: wrap and vec sweep
  c_cc_wrap: cover property (disable iff (reset) $past(count_reg) == 4'hF && count_reg == 4'h0);
  c_cc_vecs: cover property (vec == 2'b00 ##1 vec == 2'b01 ##1 vec == 2'b10 ##1 vec == 2'b11);
endmodule

bind counter_combination cc_sva cc_sva_b();


// Assertions for top_module
module top_sva;
  default clocking cb @(posedge clk); endclocking

  // Structural/wiring checks
  a_top_outv_link:      assert property (outv == final_out);
  a_top_and_msb_zero:   assert property (and_out[3:2] == 2'b00);         // vec is 2-bit -> MSBs zero-extended
  a_top_ctr_low_zero:   assert property (counter_out[1:0] == 2'b00);     // inherited from submodule behavior
  a_top_and_all_zero:   assert property (and_out == 4'b0000);            // given above invariants
  a_top_final_constant: assert property (final_out == 4'b1100);          // thus outv is 4'b1100
  a_top_o_map:          assert property ({o1,o0} == {counter_out[3], counter_out[2]});

  // No X/Z after reset
  a_top_no_x: assert property (disable iff (reset)
                               !$isunknown({outv, o1, o0, and_out, final_out, counter_out}));

  // Coverage: observe both o1 levels
  c_top_o1_hi: cover property (disable iff (reset) o1);
  c_top_o1_lo: cover property (disable iff (reset) !o1);
endmodule

bind top_module top_sva top_sva_b();
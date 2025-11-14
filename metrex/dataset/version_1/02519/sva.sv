// SystemVerilog Assertions for my_dff and shift_register_adder

// ---------------------- my_dff SVA ----------------------
bind my_dff my_dff_sva dff_sva();

module my_dff_sva;
  default clocking cb @(posedge clk); endclocking

  // q must equal d from previous rising edge (ignore first cycle/unknown)
  property p_q_follows_d;
    !$isunknown($past(d)) |-> q == $past(d);
  endproperty
  assert property (p_q_follows_d)
    else $error("my_dff: q != $past(d)");

  // No glitches away from posedge
  assert property (@(negedge clk) $stable(q))
    else $error("my_dff: q changed off posedge clk");

  // Coverage: observe q activity
  cover property ($rose(q));
  cover property ($fell(q));
  cover property ($changed(q));
endmodule


// ---------------- shift_register_adder SVA ----------------
bind shift_register_adder shift_register_adder_sva sra_sva();

module shift_register_adder_sva;
  default clocking cb @(posedge clk); endclocking

  // No X/Z on critical signals
  assert property (!$isunknown({adder_input, d, shift_reg, shifted_input, adder_output, sum}))
    else $error("shift_register_adder: X/Z detected on key nets");

  // Combinational spec checks
  assert property (shifted_input == {1'b0, shift_reg[2:0], 1'b0})
    else $error("shift_register_adder: shifted_input mismatch");

  assert property (adder_output == adder_input + shifted_input)
    else $error("shift_register_adder: adder_output mismatch");

  // sum is only 7 bits; it must equal the low 7 bits of {adder_output, shift_reg}
  assert property (sum == {adder_output[2:0], shift_reg})
    else $error("shift_register_adder: sum concatenation mismatch");

  // Guard against information loss due to truncation into 7 bits
  assert property (adder_output[4:3] == 2'b00)
    else $error("shift_register_adder: sum truncates non-zero MSBs from adder_output");

  // If drivers are stable, outputs must be stable (combinational sanity)
  assert property ($stable({shift_reg, adder_input, d}) |-> $stable({shifted_input, adder_output, sum}))
    else $error("shift_register_adder: outputs changed while inputs stable");

  // Coverage: key value scenarios and potential truncation
  cover property (sum == 7'h00);
  cover property (sum == 7'h7F);
  cover property (adder_input == 4'h0 && shift_reg == 4'h0);
  cover property (adder_input == 4'hF && shift_reg == 4'hF);
  cover property (adder_output[4:3] != 2'b00); // hits when truncation would occur
  cover property ($changed(sum));
  cover property ($rose(d));
  cover property ($fell(d));
endmodule
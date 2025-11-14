// Bind these assertions into the DUT
bind shift_register shift_register_sva();

// SVA checker (binds into shift_register scope and can see its signals)
module shift_register_sva;

  default clocking cb @(posedge clk); endclocking

  // Zero-extension at stage1 when input is known
  a_stage1_zero_extend: assert property (!$isunknown(in) |-> stage1_out == {2'b00, in});

  // Pipeline register-to-register propagation (case equality tolerates X during startup)
  a_stage2_follows: assert property (stage2_out === $past(stage1_out));
  a_out_follows:    assert property (out        === $past(stage2_out));

  // End-to-end behavior: out is in delayed by 3 cycles and zero-extended
  a_end_to_end: assert property (!$isunknown($past(in,3)) |-> out == {2'b00, $past(in,3)});

  // Upper bits must be zero whenever known
  a_stage1_upper_zero: assert property (!$isunknown(stage1_out) |-> stage1_out[2:1] == 2'b00);
  a_stage2_upper_zero: assert property (!$isunknown(stage2_out) |-> stage2_out[2:1] == 2'b00);
  a_out_upper_zero:    assert property (!$isunknown(out)        |-> out[2:1]        == 2'b00);

  // Functional coverage: exercise both data values and transitions through the 3-cycle pipeline
  c_in0_prop:   cover property (in == 1'b0 ##3 out == 3'b000);
  c_in1_prop:   cover property (in == 1'b1 ##3 out == 3'b001);
  c_0to1_prop:  cover property (in == 1'b0 ##1 in == 1'b1 ##3 out == 3'b001);
  c_1to0_prop:  cover property (in == 1'b1 ##1 in == 1'b0 ##3 out == 3'b000);

endmodule
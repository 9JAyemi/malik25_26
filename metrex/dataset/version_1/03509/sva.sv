// SVA for and_gate
// Bind this checker to the DUT to verify functionality and provide concise coverage.

module and_gate_sva (and_gate dut);

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff ($initstate);

  // Sanity: no X/Z on sampled inputs/outputs
  a_inputs_known: assert property (!$isunknown({dut.a, dut.b}));
  out_known:     assert property (!$isunknown(dut.out));

  // Combinational AND correctness at the mux
  mux_func:      assert property (dut.mux_out === (dut.a & dut.b));

  // FF captures mux_out (1-cycle latency)
  dff_loads_mux: assert property (dut.d_ff_out === $past(dut.mux_out));

  // Output mirrors FF
  out_mirror:    assert property (dut.out === dut.d_ff_out);

  // Functional spec: out equals prior-cycle (a & b)
  out_function:  assert property (dut.out === ($past(dut.a) & $past(dut.b)));

  // Output changes only while clk is high (i.e., right after posedge)
  always @(dut.out) begin
    if (!$isunknown(dut.out) && !$isunknown(dut.clk)) assert (dut.clk === 1'b1);
  end

  // Coverage: exercise inputs, pipeline effect, and output toggles
  cover_inputs00: cover property ({dut.a,dut.b}==2'b00);
  cover_inputs01: cover property ({dut.a,dut.b}==2'b01);
  cover_inputs10: cover property ({dut.a,dut.b}==2'b10);
  cover_inputs11: cover property ({dut.a,dut.b}==2'b11);
  cover_pipe_hi:  cover property ((dut.a & dut.b) ##1 dut.out);
  cover_out1:     cover property (dut.out);
  cover_out0:     cover property (!dut.out);
  cover_rise:     cover property ($rose(dut.out));
  cover_fall:     cover property ($fell(dut.out));

endmodule

bind and_gate and_gate_sva and_gate_sva_i (.dut());
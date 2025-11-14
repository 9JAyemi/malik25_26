// SVA checker bound to the DUT. Focused, high-quality assertions and essential coverage.

bind pipeline_module pipeline_module_sva sva();

module pipeline_module_sva (pipeline_module dut);

  default clocking cb @(posedge dut.clk); endclocking

  // Warm-up flags to safely use $past() without reset
  bit s1, s2, s3;
  always @(posedge dut.clk) begin
    s1 <= 1'b1;
    s2 <= s1;
    s3 <= s2;
  end

  // Combinational mapping checks
  a_outv_map:  assert property (dut.outv == dut.reg3);
  a_o2_map:    assert property (dut.o2   == dut.reg3[2]);
  a_o1_map:    assert property (dut.o1   == dut.reg2[1]);
  a_o0_map:    assert property (dut.o0   == dut.reg1[0]);

  // Per-stage pipeline capture checks
  a_reg1_cap:  assert property (s1 |-> (dut.reg1 == $past(dut.vec)));
  a_reg2_cap:  assert property (s2 |-> (dut.reg2 == $past(dut.reg1)));
  a_reg3_cap:  assert property (s3 |-> (dut.reg3 == $past(dut.reg2)));

  // End-to-end latency vs input
  a_outv_lat:  assert property (s3 |-> (dut.outv     == $past(dut.vec,3)));
  a_o2_lat:    assert property (s3 |-> (dut.o2       == $past(dut.vec[2],3)));
  a_o1_lat:    assert property (s2 |-> (dut.o1       == $past(dut.vec[1],2)));
  a_o0_lat:    assert property (s1 |-> (dut.o0       == $past(dut.vec[0],1)));

  // Cross-output temporal relations
  a_o2_eq_outv2:    assert property (dut.o2 == dut.outv[2]);
  a_o1_prev_outv1:  assert property (s1 |-> (dut.o1 == $past(dut.outv[1])));
  a_o0_prev2_outv0: assert property (s2 |-> (dut.o0 == $past(dut.outv[0],2)));

  // Sanity: no X/Z after pipeline warm-up
  a_no_x_after_warmup: assert property (s3 |-> !$isunknown({dut.reg1,dut.reg2,dut.reg3,dut.outv,dut.o2,dut.o1,dut.o0}));

  // Functional coverage: propagation and per-bit latencies
  c_vec_to_outv: cover property (s3 and $changed(dut.vec) ##3 (dut.outv == $past(dut.vec,3)));
  c_b0_rise:     cover property (s1 and $rose(dut.vec[0]) ##1 $rose(dut.o0));
  c_b1_rise:     cover property (s2 and $rose(dut.vec[1]) ##2 $rose(dut.o1));
  c_b2_rise:     cover property (s3 and $rose(dut.vec[2]) ##3 $rose(dut.o2));
  c_b0_fall:     cover property (s1 and $fell(dut.vec[0]) ##1 $fell(dut.o0));
  c_b1_fall:     cover property (s2 and $fell(dut.vec[1]) ##2 $fell(dut.o1));
  c_b2_fall:     cover property (s3 and $fell(dut.vec[2]) ##3 $fell(dut.o2));

endmodule
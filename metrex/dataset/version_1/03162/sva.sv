// SVA for t2: concise, complete transition checking and output correctness.
// Bind this module to the DUT: bind t2 t2_sva t2_sva_inst();

module t2_sva (t2 dut);

  localparam [1:0] S0 = dut.S0, S1 = dut.S1, S2 = dut.S2, S3 = dut.S3;

  // Initial state (simulation/formal)
  initial assert (dut.state == S0);

  // State encoding stays valid
  assert property (@(posedge dut.clks[0]) dut.state inside {S0,S1,S2,S3});

  // Complete transition relation on clks[0]
  // S0
  assert property (@(posedge dut.clks[0]) (dut.state==S0 &&  dut.c0 && !dut.c1) |=> dut.state==S1);
  assert property (@(posedge dut.clks[0]) (dut.state==S0 && !dut.c0 &&  dut.c1) |=> dut.state==S2);
  assert property (@(posedge dut.clks[0]) (dut.state==S0 && (dut.c0==dut.c1))   |=> dut.state==S0);
  // S1
  assert property (@(posedge dut.clks[0]) (dut.state==S1 &&  dut.c0 && !dut.c1) |=> dut.state==S3);
  assert property (@(posedge dut.clks[0]) (dut.state==S1 && !dut.c0 && !dut.c1) |=> dut.state==S0);
  assert property (@(posedge dut.clks[0]) (dut.state==S1 &&  dut.c1)            |=> dut.state==S1);
  // S2
  assert property (@(posedge dut.clks[0]) (dut.state==S2 && !dut.c0 &&  dut.c1) |=> dut.state==S3);
  assert property (@(posedge dut.clks[0]) (dut.state==S2 &&  dut.c0 && !dut.c1) |=> dut.state==S0);
  assert property (@(posedge dut.clks[0]) (dut.state==S2 && (dut.c0==dut.c1))   |=> dut.state==S2);
  // S3
  assert property (@(posedge dut.clks[0]) (dut.state==S3 && !dut.c0 && !dut.c1) |=> dut.state==S2);
  assert property (@(posedge dut.clks[0]) (dut.state==S3 &&  dut.c0 &&  dut.c1) |=> dut.state==S1);
  assert property (@(posedge dut.clks[0]) (dut.state==S3 && (dut.c0!=dut.c1))   |=> dut.state==S3);

  // Output correctness on clks[1]
  assert property (@(posedge dut.clks[1]) dut.o_check == (dut.state==S3 && dut.check));

  // Minimal X-safety on internal state/output at their clocks
  assert property (@(posedge dut.clks[0]) !$isunknown(dut.state));
  assert property (@(posedge dut.clks[1]) !$isunknown(dut.o_check));

  // Coverage
  cover property (@(posedge dut.clks[0]) dut.state==S0 ##1 dut.state==S1 ##1 dut.state==S3 ##1 dut.state==S2 ##1 dut.state==S0);
  cover property (@(posedge dut.clks[0]) (dut.state==S1 && dut.c0 && !dut.c1) ##1 (dut.state==S3));
  cover property (@(posedge dut.clks[0]) (dut.state==S2 && !dut.c0 && dut.c1) ##1 (dut.state==S3));
  cover property (@(posedge dut.clks[1]) (dut.state==S3 && dut.check && dut.o_check));

endmodule
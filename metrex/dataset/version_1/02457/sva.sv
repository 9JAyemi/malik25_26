// SVA for regfile
// Bind into the DUT for internal rf[] visibility
bind regfile regfile_sva u_regfile_sva();

module regfile_sva();
  // Implicitly in the scope of regfile instance: can refer to clk, resetn, rf, etc.
  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetn);

  // ------------------------
  // Functional correctness
  // ------------------------

  // Asynchronous read mappings (sampled on clock edges)
  assert property ( (raddr1 == 5'd0) |-> (rdata1 == 32'd0) );
  assert property ( (raddr1 != 5'd0) |-> (rdata1 == rf[raddr1]) );

  assert property ( (raddr2 == 5'd0) |-> (rdata2 == 32'd0) );
  assert property ( (raddr2 != 5'd0) |-> (rdata2 == rf[raddr2]) );

  assert property ( (test_addr == 5'd0) |-> (test_data == 32'd0) );
  assert property ( (test_addr != 5'd0) |-> (test_data == rf[test_addr]) );

  // Synchronous write updates array one cycle later
  assert property ( wen |=> (rf[$past(waddr)] == $past(wdata)) );

  // No-write preserves array contents
  assert property ( !wen |=> (foreach (rf[i]) (rf[i] == $past(rf[i]))) );

  // Reset dominates: on a cycle with reset asserted, all registers are 0 next cycle
  // (no disable on reset for this check)
  assert property (@cb (!resetn) |=> (foreach (rf[i]) (rf[i] == 32'd0)));

  // Known outputs when not in reset
  assert property ( !$isunknown({rdata1, rdata2, test_data}) );

  // Read-after-write to same address returns the written data next cycle
  assert property ( wen ##1 (raddr1 == $past(waddr)) |-> (rdata1 == $past(wdata)) );
  assert property ( wen ##1 (raddr2 == $past(waddr)) |-> (rdata2 == $past(wdata)) );
  assert property ( wen ##1 (test_addr == $past(waddr)) |-> (test_data == $past(wdata)) );

  // ------------------------
  // Coverage
  // ------------------------

  // Observe a reset pulse
  cover property (@cb !resetn ##1 resetn);

  // Exercise writes to all locations
  genvar wi;
  generate
    for (wi = 0; wi < 32; wi++) begin : C_WRITE_EACH_ADDR
      cover property (@cb wen && (waddr == wi[4:0]));
    end
  endgenerate

  // Simultaneous same/different read addresses
  cover property (@cb (raddr1 == raddr2));
  cover property (@cb (raddr1 != raddr2));

  // Write followed by both read ports reading that address next cycle
  cover property (@cb wen ##1 (raddr1 == $past(waddr) && raddr2 == $past(waddr)));

endmodule
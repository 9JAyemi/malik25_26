module my_module_sva (
  input logic in0, in1, in2, in3,
  input logic d0, d1, d2, d3,
  input logic clk, reset,
  input logic out0, out1, out2, out3
);

  ///// Registering behavior /////
  // out0 equals d0 from the previous cycle.
  check_out0_registers_d0: assert property (
    @(posedge clk) disable iff (reset) out0 == $past(d0)
  );
  // out1 equals d1 from the previous cycle.
  check_out1_registers_d1: assert property (
    @(posedge clk) disable iff (reset) out1 == $past(d1)
  );
  // out2 equals d2 from the previous cycle.
  check_out2_registers_d2: assert property (
    @(posedge clk) disable iff (reset) out2 == $past(d2)
  );
  // out3 equals d3 from the previous cycle.
  check_out3_registers_d3: assert property (
    @(posedge clk) disable iff (reset) out3 == $past(d3)
  );

  ///// Change propagation /////
  // A change on d0 causes out0 to change next cycle.
  change_out0_follows_d0_change: assert property (
    @(posedge clk) disable iff (reset) $changed(d0) |=> $changed(out0)
  );
  // A change on d1 causes out1 to change next cycle.
  change_out1_follows_d1_change: assert property (
    @(posedge clk) disable iff (reset) $changed(d1) |=> $changed(out1)
  );
  // A change on d2 causes out2 to change next cycle.
  change_out2_follows_d2_change: assert property (
    @(posedge clk) disable iff (reset) $changed(d2) |=> $changed(out2)
  );
  // A change on d3 causes out3 to change next cycle.
  change_out3_follows_d3_change: assert property (
    @(posedge clk) disable iff (reset) $changed(d3) |=> $changed(out3)
  );

  ///// Stability propagation /////
  // If d0 is stable, out0 stays stable next cycle.
  stable_out0_when_d0_stable: assert property (
    @(posedge clk) disable iff (reset) !$changed(d0) |=> !$changed(out0)
  );
  // If d1 is stable, out1 stays stable next cycle.
  stable_out1_when_d1_stable: assert property (
    @(posedge clk) disable iff (reset) !$changed(d1) |=> !$changed(out1)
  );
  // If d2 is stable, out2 stays stable next cycle.
  stable_out2_when_d2_stable: assert property (
    @(posedge clk) disable iff (reset) !$changed(d2) |=> !$changed(out2)
  );
  // If d3 is stable, out3 stays stable next cycle.
  stable_out3_when_d3_stable: assert property (
    @(posedge clk) disable iff (reset) !$changed(d3) |=> !$changed(out3)
  );

endmodule
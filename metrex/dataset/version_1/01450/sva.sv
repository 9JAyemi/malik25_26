// SVA for system_controller
// Bind-in, concise, and focused on key behavior and coverage.

module system_controller_sva_bind;
  bind system_controller system_controller_sva_chk u_system_controller_sva_chk();
endmodule

module system_controller_sva_chk (system_controller dut);

  default clocking cb @(posedge dut.clk_in); endclocking

  wire cond = dut.reset_in || !dut.locked;  // reset condition driving the counter and reset_sys

  // Combinational equivalence of reset_sys
  assert property (dut.reset_sys == (dut.reset_in || !dut.locked || (|dut.reset_count)))
    else $error("reset_sys equation violated");

  // On cond, next reset_count must be 1; while cond stays high, reset_count must hold at 1
  assert property (cond |-> ##1 (dut.reset_count == 6'h1))
    else $error("reset_count not set to 1 on cond");
  assert property (cond && $past(cond) |-> (dut.reset_count == 6'h1))
    else $error("reset_count failed to hold 1 while cond asserted");

  // When cond is low and counter nonzero, it increments modulo-64 each cycle
  assert property (!cond && (dut.reset_count != 6'h0) |-> ##1 (dut.reset_count == $past(dut.reset_count) + 6'h1))
    else $error("reset_count failed to increment");

  // When cond is low and counter zero, it holds at zero
  assert property (!cond && (dut.reset_count == 6'h0) |-> ##1 (dut.reset_count == 6'h0))
    else $error("reset_count failed to hold at zero");

  // With cond low and reset_count==1, reset_sys stretches exactly 63 cycles then deasserts (unless cond reasserts)
  assert property (disable iff (cond)
                   (!cond && dut.reset_count == 6'h1) |-> ( !cond && dut.reset_sys )[*63] ##1 (!dut.reset_sys))
    else $error("reset_sys stretch length violation");

  // No unknowns on key control/state at clock edges
  assert property (!$isunknown({dut.reset_sys, dut.locked, dut.reset_count})));

`ifndef XILINX
  // In non-Xilinx build: locked is constant 1 and clk_sys mirrors clk_in
  assert property (dut.locked === 1'b1)
    else $error("locked must be 1 in non-XILINX build");
  assert property (@(posedge dut.clk_in or negedge dut.clk_in) (dut.clk_sys === dut.clk_in))
    else $error("clk_sys must equal clk_in in non-XILINX build");
`endif

  // Functional coverage
  cover property ($rose(cond));
  cover property ($fell(cond));
  cover property (disable iff (cond) (!cond && dut.reset_count == 6'h1) ##63 (!cond && dut.reset_count == 6'h0)); // rollover observed
  cover property (!cond && dut.reset_count == 6'h3F); // near wrap

endmodule
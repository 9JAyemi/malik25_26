// SVA for up_down_counter_shifter
// Bindable checker that uses hierarchical access to DUT internals.
module up_down_counter_shifter_sva (up_down_counter_shifter dut);

  default clocking @(posedge dut.CLK); endclocking

  // Basic structural check
  assert property (dut.Q == dut.counter);

  // Synchronous reset behavior
  assert property (dut.RST |-> (dut.counter == 4'h0 && dut.RESULT == 4'h0));

  // Clean (no X/Z) after reset is deasserted
  assert property (disable iff (dut.RST) !$isunknown({dut.UP,dut.DOWN,dut.SHIFT,dut.B}));
  assert property (disable iff (dut.RST) !$isunknown({dut.counter,dut.RESULT,dut.Q}));

  // Counter update rules
  assert property (disable iff (dut.RST)
                   (dut.UP && !dut.DOWN) |-> dut.counter == $past(dut.counter) + 4'h1);
  assert property (disable iff (dut.RST)
                   (!dut.UP && dut.DOWN) |-> dut.counter == $past(dut.counter) - 4'h1);
  assert property (disable iff (dut.RST)
                   (!(dut.UP ^ dut.DOWN)) |-> dut.counter == $past(dut.counter));

  // RESULT update rules (note: RHS uses pre-update counter due to NBA semantics)
  assert property (disable iff (dut.RST)
                   dut.SHIFT |-> dut.RESULT == ($past(dut.counter) << dut.B));
  assert property (disable iff (dut.RST)
                   !dut.SHIFT |-> dut.RESULT == $past(dut.counter));

  // Large shift amounts zero out 4-bit result (redundant but explicit)
  assert property (disable iff (dut.RST)
                   (dut.SHIFT && (dut.B >= 4)) |-> dut.RESULT == 4'h0);

  // Coverage: exercise all branches, wrap, and key shift cases
  cover property ($rose(dut.RST));
  cover property (disable iff (dut.RST) (dut.UP && !dut.DOWN));
  cover property (disable iff (dut.RST) (!dut.UP && dut.DOWN));
  cover property (disable iff (dut.RST) (dut.UP && dut.DOWN));
  cover property (disable iff (dut.RST) (!dut.UP && !dut.DOWN));
  cover property (disable iff (dut.RST)
                  (dut.counter == 4'hF && dut.UP && !dut.DOWN) |=> dut.counter == 4'h0);
  cover property (disable iff (dut.RST)
                  (dut.counter == 4'h0 && !dut.UP && dut.DOWN) |=> dut.counter == 4'hF);
  cover property (disable iff (dut.RST) (dut.SHIFT && (dut.B == 0)));
  cover property (disable iff (dut.RST) (dut.SHIFT && (dut.B == 1)));
  cover property (disable iff (dut.RST) (dut.SHIFT && (dut.B >= 4)));

endmodule

// Bind into all instances of the DUT
bind up_down_counter_shifter up_down_counter_shifter_sva sva_i (.*);
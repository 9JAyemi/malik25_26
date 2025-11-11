// Bindable SVA checker for shift_register
bind shift_register shift_register_sva svas(.dut(this));

module shift_register_sva (shift_register dut);

  default clocking cb @(posedge dut.clk); endclocking

  // Basic sanity
  assert property (!$isunknown({dut.load, dut.valid, dut.out}));

  // Combinational mapping
  assert property (dut.out == dut.reg4);

  // valid mirrors load
  assert property (dut.valid == dut.load);

  // Cycle-to-cycle transfers on load
  assert property (dut.load |-> {dut.reg4,dut.reg3,dut.reg2,dut.reg1} ==
                              {$past(dut.reg3,1,'0), $past(dut.reg2,1,'0), $past(dut.reg1,1,'0), $past(dut.in,1,'0)});

  // Cycle-to-cycle transfers on no-load
  assert property (!dut.load |-> {dut.reg4,dut.reg3,dut.reg2,dut.reg1} ==
                               {4'b0, $past(dut.reg4,1,'0), $past(dut.reg3,1,'0), $past(dut.reg2,1,'0)});

  // Forward latency under continuous load: out reflects in after 3 cycles
  assert property (dut.load[*4] |-> (dut.out == $past(dut.in,3,'0)));

  // Coverage
  cover property (dut.load);
  cover property (!dut.load);
  cover property (dut.load[*4] ##1 (dut.out == $past(dut.in,3,'0)));
  cover property (!dut.load[*4] ##1 ({dut.reg4,dut.reg3,dut.reg2,dut.reg1} == 16'b0));

endmodule
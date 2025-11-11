// Bind these SVA into the DUT scope
bind Datapath_RegisterFile Datapath_RegisterFile_sva sva_inst();

module Datapath_RegisterFile_sva;
  // Runs in Datapath_RegisterFile scope; has direct access to REGS, etc.
  default clocking cb @(posedge CLK); endclocking

  // Combinational read-port correctness (checks after sequential updates in same cycle)
  assert property (1'b1 |-> ##0 (A_data == REGS[AA]));
  assert property (1'b1 |-> ##0 (B_data == REGS[BA]));

  // Same-cycle write-through to read ports
  assert property (RW && (DA == AA) |-> ##0 (A_data == D_data));
  assert property (RW && (DA == BA) |-> ##0 (B_data == D_data));

  // Register-file write/update semantics
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : g_rf
      // If RW hits i, that reg updates next cycle to D_data
      assert property (RW && (DA == i) |=> (REGS[i] == $past(D_data)));
      // If RW misses i, that reg holds its value
      assert property (RW && (DA != i) |=> (REGS[i] == $past(REGS[i])));
      // If !RW, no regs change
      assert property (!RW |=> (REGS[i] == $past(REGS[i])));

      // Coverage: writes and reads to every address
      cover property (RW && (DA == i));
      cover property (AA == i);
      cover property (BA == i);
      // Coverage: same-cycle write-through observed on each port
      cover property (RW && (DA == i) && (AA == i));
      cover property (RW && (DA == i) && (BA == i));
    end
  endgenerate

  // Additional, concise cross coverage
  cover property (!RW);
  cover property (AA != BA);
  cover property (RW && (DA == AA) && (DA == BA));
endmodule
// SVA for memoryaccess
bind memoryaccess memoryaccess_sva macc_sva();

module memoryaccess_sva();
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Passthrough/latching
  assert property (past_valid |-> ALUResultOut == $past(ALUResultIn));
  assert property (past_valid |-> MemToRegM2   == $past(MemToRegM1));
  assert property (past_valid |-> RegWriteM2   == $past(RegWriteM1));
  assert property (past_valid |-> WriteRegM2   == $past(WriteRegM1));

  // Branch/PC logic
  assert property (past_valid |-> PCSrcM == $past(BranchM && ZerowireM));
  assert property (past_valid |-> PCBranchM2 == $past((BranchM && ZerowireM) ? (PCBranchM1 + ALUResultIn) : PCBranchM1));

  // Read path (read old mem value; holds when not reading)
  assert property (past_valid && $past(MemToRegM1) |-> ReadDataM == $past(mem[$past(ALUResultIn[9:2])]));
  assert property (past_valid && !$past(MemToRegM1) |-> ReadDataM == $past(ReadDataM));

  // Write path (write updates addressed location; holds when not writing)
  assert property (past_valid && $past(MemWriteM) |-> mem[$past(ALUResultIn[9:2])] == $past(WriteDataM));
  assert property (past_valid && !$past(MemWriteM) |-> mem[$past(ALUResultIn[9:2])] == $past(mem[$past(ALUResultIn[9:2])]));

  // Outputs change only on clock edge
  assert property (@(negedge clk) $stable({ReadDataM, ALUResultOut, PCBranchM2, WriteRegM2, RegWriteM2, MemToRegM2, PCSrcM}));

  // Key coverage
  cover property (past_valid && MemWriteM);
  cover property (past_valid && MemToRegM1);
  cover property (past_valid && MemWriteM && MemToRegM1); // same-cycle write+read
  cover property (past_valid && BranchM && ZerowireM);    // branch taken
  cover property (past_valid && BranchM && !ZerowireM);   // branch not taken
  cover property (past_valid && MemWriteM && (ALUResultIn[9:2] == 8'h00));
  cover property (past_valid && MemWriteM && (ALUResultIn[9:2] == 8'hFF));
endmodule
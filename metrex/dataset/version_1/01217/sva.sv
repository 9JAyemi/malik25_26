// SVA checker for communication_module
// Bind this module to the DUT:  bind communication_module communication_module_sva sva_comm();

module communication_module_sva;

  // Access DUT scope signals directly via bind
  default clocking cb @(posedge clk); endclocking
  // Disable most checks while in reset
  default disable iff (rst);

  // -------------------------
  // Basic sanity
  // -------------------------
  // legal state encoding
  assert property (state_reg inside {est0,est1,est2,est3,est4,est5,est6,est7,est8,est9,est10,est11});
  // no X on state or outputs
  assert property (!$isunknown(state_reg));
  assert property (!$isunknown({beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}));
  // reset puts FSM in est0 (checked at clock edges)
  assert property (@(posedge clk) rst |-> state_reg==est0);

  // -------------------------
  // State transitions (next-cycle)
  // -------------------------
  assert property (state_reg==est0  |=> state_reg==est1);
  assert property (state_reg==est1  |=> state_reg==est2);
  assert property (state_reg==est2  |=> state_reg==est3);
  assert property (state_reg==est3  |=> state_reg==est4);
  assert property ((state_reg==est4 && !ready_op) |=> state_reg==est4);
  assert property ((state_reg==est4 &&  ready_op) |=> state_reg==est5);
  assert property (state_reg==est5  |=> state_reg==est6);
  assert property (state_reg==est6  |=> state_reg==est7);
  assert property ((state_reg==est7 && !TX_DONE)                |=> state_reg==est7);
  assert property ((state_reg==est7 &&  TX_DONE && !max_tick_ch)|=> state_reg==est8);
  assert property ((state_reg==est7 &&  TX_DONE &&  max_tick_ch)|=> state_reg==est9);
  assert property (state_reg==est8  |=> state_reg==est5);
  assert property ((state_reg==est9 &&  max_tick_address) |=> state_reg==est11));
  assert property ((state_reg==est9 && !max_tick_address) |=> state_reg==est10));
  assert property (state_reg==est10 |=> state_reg==est2);
  assert property (state_reg==est11 |=> state_reg==est11);

  // -------------------------
  // Output decode per state (exact match)
  // Vector order: {beg_op, ack_op, load_address, enab_address, enab_ch, load_ch, TX_START}
  // -------------------------
  assert property (state_reg==est0  |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b0000000);
  assert property (state_reg==est1  |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b0011000);
  assert property (state_reg==est2  |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b1000000);
  assert property (state_reg==est3  |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b1000110);
  assert property (state_reg==est4  |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b0000000);
  assert property (state_reg==est5  |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b0000000);
  assert property (state_reg==est6  |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b0000001);
  assert property (state_reg==est7  |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b0000000);
  assert property (state_reg==est8  |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b0000100);
  assert property (state_reg==est9  |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b0000000);
  assert property (state_reg==est10 |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b0101000);
  assert property (state_reg==est11 |-> {beg_op,ack_op,load_address,enab_address,enab_ch,load_ch,TX_START}==7'b0000000);

  // Outputs imply valid state(s)
  assert property (ack_op       |-> state_reg==est10);
  assert property (load_address |-> state_reg==est1);
  assert property (load_ch      |-> state_reg==est3);
  assert property (TX_START     |-> state_reg==est6);
  assert property (enab_ch      |-> (state_reg inside {est3,est8}));
  assert property (enab_address |-> (state_reg inside {est1,est10}));
  assert property (beg_op       |-> (state_reg inside {est2,est3}));

  // -------------------------
  // Pulse width/shape checks
  // -------------------------
  assert property ($rose(load_address) |-> ##1 !load_address);
  assert property ($rose(load_ch)      |-> ##1 !load_ch);
  assert property ($rose(ack_op)       |-> ##1 !ack_op);
  assert property ($rose(TX_START)     |-> ##1 !TX_START);
  assert property ($rose(enab_ch)      |-> ##1 !enab_ch);
  assert property ($rose(enab_address) |-> ##1 !enab_address);
  // beg_op is exactly 2 cycles (est2, est3)
  assert property ($rose(beg_op) |-> beg_op ##1 beg_op ##1 !beg_op);

  // -------------------------
  // Key functional coverage
  // -------------------------
  // Ready path to TX_START
  cover property (state_reg==est4 && ready_op ##1 state_reg==est5 ##1 state_reg==est6 && TX_START);
  // Channel iterate (not last channel)
  cover property (state_reg==est7 && TX_DONE && !max_tick_ch ##1 state_reg==est8 ##1 state_reg==est5);
  // Channel last -> address handling
  cover property (state_reg==est7 && TX_DONE &&  max_tick_ch ##1 state_reg==est9);
  // Address not last -> continue operation
  cover property (state_reg==est9 && !max_tick_address ##1 state_reg==est10 && ack_op ##1 state_reg==est2);
  // Address last -> terminal state
  cover property (state_reg==est9 &&  max_tick_address ##1 state_reg==est11);

endmodule

// Bind line example (place outside DUT, e.g., in a testbench or a package):
// bind communication_module communication_module_sva sva_comm();
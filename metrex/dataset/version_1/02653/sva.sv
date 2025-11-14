// SVA for ram_control
// Bind these assertions to the DUT; concise but checks key behaviors.

module ram_control_assertions;

  // Access DUT scope via bind; all identifiers below refer to ram_control signals
  bit inited;
  initial inited = 1'b0;
  always @(posedge clk) inited <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!inited);

  // Basic input sanity (no X/Z on driving inputs)
  a_no_x_inputs: assert property (!$isunknown({enable, addrA, addrB, addrW, dataIn})));

  // When disabled, outputs hold their value
  a_hold_when_disabled: assert property (!enable |=> $stable({dataOutA, dataOutB})));

  // Synchronous read: outputs reflect previous-cycle RAM value at current addresses
  a_readA_sync: assert property (enable |=> dataOutA == $past(ram[addrA])));
  a_readB_sync: assert property (enable |=> dataOutB == $past(ram[addrB])));

  // Synchronous write: RAM at write address updates with previous-cycle dataIn
  a_write_sync: assert property (enable |=> ram[$past(addrW)] == $past(dataIn)));

  // No write when disabled at addressed location (value holds)
  a_no_write_when_disabled: assert property (!enable |=> ram[$past(addrW)] == $past(ram[addrW])));

  // If both read ports target same address, they return same value
  a_same_addr_same_data: assert property (enable && (addrA == addrB) |=> dataOutA == dataOutB));

  // Read-during-write to same address returns old data (read-before-write semantics)
  a_collision_A_old: assert property (enable && (addrA == addrW) |=> dataOutA == $past(ram[addrA])));
  a_collision_B_old: assert property (enable && (addrB == addrW) |=> dataOutB == $past(ram[addrB])));

  // Outputs only change on cycles where enable was asserted
  a_outputs_only_update_on_enable: assert property ($changed({dataOutA, dataOutB}) |-> $past(enable)));

  // -----------------
  // Coverage (key scenarios)
  // -----------------
  // Back-to-back enabled cycles
  c_back_to_back_enable: cover property (enable ##1 enable);

  // Write then read-back on A next cycle
  property p_rawA_next;
    logic [11:0] a; logic [8:0] d;
    (enable, a = addrW, d = dataIn) ##1 (enable && (addrA == a)) ##1 (dataOutA == d);
  endproperty
  c_rawA_next: cover property (p_rawA_next);

  // Write then read-back on B next cycle
  property p_rawB_next;
    logic [11:0] a; logic [8:0] d;
    (enable, a = addrW, d = dataIn) ##1 (enable && (addrB == a)) ##1 (dataOutB == d);
  endproperty
  c_rawB_next: cover property (p_rawB_next);

  // Read-during-write collision on A and B
  c_collision_A: cover property (enable && (addrA == addrW));
  c_collision_B: cover property (enable && (addrB == addrW));

  // Both read ports same address
  c_same_read_addr: cover property (enable && (addrA == addrB));

endmodule

bind ram_control ram_control_assertions u_ram_control_assertions();
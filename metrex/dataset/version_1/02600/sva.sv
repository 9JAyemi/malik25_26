// SVA for feedforward_p_uOut_ram
module ff_uOut_ram_sva #(parameter DWIDTH=64, AWIDTH=8, MEM_SIZE=140) ();
  // Implicitly bound into feedforward_p_uOut_ram scope; direct access to DUT signals
  default clocking @(posedge clk); endclocking

  // Basic sanity and range
  ap_ctrl_known:     assert property (!$isunknown({ce0,we0,ce1})));
  ap_addr0_range:    assert property (ce0 |-> (addr0 < MEM_SIZE));
  ap_addr1_range:    assert property (ce1 |-> (addr1 < MEM_SIZE));
  ap_d0_known_on_wr: assert property (ce0 && we0 |-> !$isunknown(d0));

  // Port0 behavior
  ap_p0_write_q0: assert property (ce0 && we0 |-> q0 == d0);                       // write-through
  ap_p0_read_q0:  assert property (ce0 && !we0 |-> q0 == $past(ram[addr0]));       // read from pre-state RAM
  ap_q0_hold:     assert property (!ce0 |-> $stable(q0));                           // no CE0 => hold

  // Port1 behavior
  ap_p1_read_q1: assert property (ce1 |-> q1 == $past(ram[addr1]));                // read from pre-state RAM
  ap_q1_hold:    assert property (!ce1 |-> $stable(q1));                           // no CE1 => hold

  // RAM update correctness on write
  ap_ram_write: assert property (ce0 && we0 |=> ram[$past(addr0)] == $past(d0));

  // Cross-port timing: data visible to port1 next cycle after write
  ap_p1_sees_wr_next: assert property (
    (ce0 && we0) ##1 (ce1 && (addr1 == $past(addr0))) |-> (q1 == $past(d0))
  );

  // Same-port timing: data visible to port0 next cycle when reading after a write
  ap_p0_sees_wr_next: assert property (
    (ce0 && we0) ##1 (ce0 && !we0 && (addr0 == $past(addr0))) |-> (q0 == $past(d0))
  );

  // Outputs known when enabled
  ap_q0_known_on_ce: assert property (ce0 |-> !$isunknown(q0));
  ap_q1_known_on_ce: assert property (ce1 |-> !$isunknown(q1));

  // Coverage
  cp_write:                cover property (ce0 && we0);
  cp_read0:                cover property (ce0 && !we0);
  cp_read1:                cover property (ce1);
  cp_same_addr_rw:         cover property (ce0 && we0 && ce1 && (addr0 == addr1));
  cp_back_to_back_writes:  cover property ((ce0 && we0) ##1 (ce0 && we0 && (addr0 != $past(addr0))));
  cp_boundary_wr0:         cover property (ce0 && we0 && (addr0 == '0));
  cp_boundary_wr_last:     cover property (ce0 && we0 && (addr0 == MEM_SIZE-1));
  cp_boundary_rd1_0:       cover property (ce1 && (addr1 == '0));
  cp_boundary_rd1_last:    cover property (ce1 && (addr1 == MEM_SIZE-1));
  cp_p1_read_after_wr:     cover property ((ce0 && we0) ##1 (ce1 && (addr1 == $past(addr0))));
  cp_p0_read_after_wr:     cover property ((ce0 && we0) ##1 (ce0 && !we0 && (addr0 == $past(addr0))));
endmodule

// Bind into all instances of the RAM
bind feedforward_p_uOut_ram ff_uOut_ram_sva #(.DWIDTH(DWIDTH), .AWIDTH(AWIDTH), .MEM_SIZE(MEM_SIZE)) u_ff_uOut_ram_sva();
// SVA for ram_block_dual_read_single_write
// Bind into the DUT instance
bind ram_block_dual_read_single_write ram_block_dual_read_single_write_sva sva_inst();

module ram_block_dual_read_single_write_sva;

  // Assume we are bound into the DUT scope: direct access to clk, ports, and ram[]
  default clocking cb @(posedge clk); endclocking

  // Gate assertions until after first clock to avoid $past() X issues
  bit init;
  initial init = 0;
  always @(posedge clk) init <= 1;
  default disable iff (!init);

  // Static width/consistency checks (flag the DWIDTH/port width mismatch, etc.)
  initial begin
    assert ($bits(d0) == $bits(ram[0])) else $error("d0 width != RAM DWIDTH");
    assert ($bits(q0) == $bits(ram[0])) else $error("q0 width != RAM DWIDTH");
    assert ($bits(q1) == $bits(ram[0])) else $error("q1 width != RAM DWIDTH");
    assert ((1 << $bits(addr0)) >= $size(ram)) else $error("addr0 AWIDTH too small for MEM_SIZE");
    assert ((1 << $bits(addr1)) >= $size(ram)) else $error("addr1 AWIDTH too small for MEM_SIZE");
  end

  // Control/inputs must be known when used
  ap_known_ctrl0: assert property (ce0 |-> (!$isunknown(we0) && !$isunknown(addr0) && (!we0 || !$isunknown(d0))));
  ap_known_ctrl1: assert property (ce1 |-> !$isunknown(addr1));

  // Outputs only update when CE asserted (hold their value otherwise)
  ap_q0_holds_when_ce0_low: assert property (!ce0 |=> $stable(q0));
  ap_q1_holds_when_ce1_low: assert property (!ce1 |=> $stable(q1));

  // Port-0 read behavior: next-cycle q0 equals previous RAM at addr0
  ap_rd0: assert property (ce0 |=> q0 == $past(ram[addr0]));

  // Port-1 read behavior: next-cycle q1 equals previous RAM at addr1
  ap_rd1: assert property (ce1 |=> q1 == $past(ram[addr1]));

  // Same-cycle write on port0 is read-first (q0 sees old data)
  // Covered by ap_rd0; explicitly check simultaneous we0 case
  ap_rd0_read_first_on_write: assert property ((ce0 && we0) |=> q0 == $past(ram[addr0]));

  // Simultaneous write (port0) and read (port1) to same address: port1 sees old data
  ap_wr0_rd1_same_addr_read_first: assert property ((ce0 && we0 && ce1 && addr0 == addr1) |=> q1 == $past(ram[addr1]));

  // Dual read same address: both outputs agree and match old RAM data
  ap_dual_read_same_addr: assert property ((ce0 && ce1 && addr0 == addr1) |=> (q0 == q1) && (q0 == $past(ram[addr0])));

  // Write correctness: next-cycle RAM at written address equals previous d0
  ap_wr0_updates_ram: assert property ((ce0 && we0) |=> ram[$past(addr0)] == $past(d0));

  // No unintended write to the bus-addressed location when write is inactive
  ap_no_write_when_disabled: assert property (!(ce0 && we0) |=> ram[$past(addr0)] == $past(ram[$past(addr0)]));

  // Basic functional coverage
  cp_write:                      cover property (ce0 && we0);
  cp_read0:                      cover property (ce0 && !we0);
  cp_read1:                      cover property (ce1);
  cp_dual_read_same_addr:        cover property (ce0 && ce1 && addr0 == addr1);
  cp_wr_and_rd1_same_addr:       cover property (ce0 && we0 && ce1 && addr0 == addr1);
  cp_back_to_back_writes_same:   cover property ((ce0 && we0) ##1 (ce0 && we0 && addr0 == $past(addr0)));
  cp_write_then_read0_new_data:  cover property ((ce0 && we0) ##1 (ce0 && addr0 == $past(addr0)) ##1 (ce0 && addr0 == $past(addr0,2) && q0 == $past(d0,2)));

endmodule
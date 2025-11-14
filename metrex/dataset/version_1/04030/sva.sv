// SVA for synchronous_ram_4port
// Bind this checker into the DUT: 
// bind synchronous_ram_4port synchronous_ram_4port_sva #(.aw(aw), .dw(dw)) u_sva();

module synchronous_ram_4port_sva #(parameter int aw=10, dw=32) ();

  // The checker is elaborated inside the DUT scope via bind; it can see DUT signals.
  // Sanity: this SVA assumes a 32-bit DI/DOQ split into 4 bytes.
  initial begin
    if (dw != 32) $error("synchronous_ram_4port_sva expects dw==32 (byte-lane semantics).");
  end

  default clocking cb @(posedge clk); endclocking

  // Basic input sanity when active
  a_inputs_known: assert property (ce |-> (!$isunknown(addr) && !$isunknown(di) && !$isunknown(we)))
    else $error("Unknowns on inputs when ce=1");

  // Address register update latency: captures addr on ce, holds otherwise
  a_addr_reg_update: assert property (
      addr_reg == ($past(ce) ? $past(addr) : $past(addr_reg))
  ) else $error("addr_reg update/hold mismatch");

  // Output mapping must be big-endian by byte lanes
  a_doq_map_b0: assert property (doq[31:24] == mem0[addr_reg][7:0]) else $error("DOQ[31:24] mapping wrong");
  a_doq_map_b1: assert property (doq[23:16] == mem1[addr_reg][7:0]) else $error("DOQ[23:16] mapping wrong");
  a_doq_map_b2: assert property (doq[15:08] == mem2[addr_reg][7:0]) else $error("DOQ[15:08] mapping wrong");
  a_doq_map_b3: assert property (doq[07:00] == mem3[addr_reg][7:0]) else $error("DOQ[07:00] mapping wrong");

  // Per-byte write semantics (write when ce && we[x], else hold), checked at next cycle at the written address
  a_wmem0: assert property (
      mem0[$past(addr)][7:0] == ($past(ce && we[3]) ? $past(di[31:24]) : $past(mem0[$past(addr)][7:0]))
  ) else $error("mem0 byte write/hold violation");

  a_wmem1: assert property (
      mem1[$past(addr)][7:0] == ($past(ce && we[2]) ? $past(di[23:16]) : $past(mem1[$past(addr)][7:0]))
  ) else $error("mem1 byte write/hold violation");

  a_wmem2: assert property (
      mem2[$past(addr)][7:0] == ($past(ce && we[1]) ? $past(di[15:08]) : $past(mem2[$past(addr)][7:0]))
  ) else $error("mem2 byte write/hold violation");

  a_wmem3: assert property (
      mem3[$past(addr)][7:0] == ($past(ce && we[0]) ? $past(di[07:00]) : $past(mem3[$past(addr)][7:0]))
  ) else $error("mem3 byte write/hold violation");

  // Read-after-write: one-cycle latency; next cycle DOQ reflects written bytes (others unchanged)
  a_raw: assert property (
      $past(ce) |-> doq == {
        ($past(we[3]) ? $past(di[31:24]) : $past(mem0[$past(addr)][7:0])),
        ($past(we[2]) ? $past(di[23:16]) : $past(mem1[$past(addr)][7:0])),
        ($past(we[1]) ? $past(di[15:08])  : $past(mem2[$past(addr)][7:0])),
        ($past(we[0]) ? $past(di[07:00])  : $past(mem3[$past(addr)][7:0]))
      }
  ) else $error("Read-after-write data mismatch");

  // Coverage
  c_lane3: cover property (ce && we[3]);
  c_lane2: cover property (ce && we[2]);
  c_lane1: cover property (ce && we[1]);
  c_lane0: cover property (ce && we[0]);
  c_full_write: cover property (ce && we == 4'b1111);
  c_back_to_back_same_addr: cover property (ce && (we!=0) ##1 ce && (we!=0) && (addr == $past(addr)));
  c_raw_same_addr: cover property (ce && (we!=0) ##1 ce && (addr == $past(addr)));

endmodule

bind synchronous_ram_4port synchronous_ram_4port_sva #(.aw(aw), .dw(dw)) u_synchronous_ram_4port_sva();
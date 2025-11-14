// SVA for rw_manager_ac_ROM_reg
`ifndef RW_MANAGER_AC_ROM_REG_SVA
`define RW_MANAGER_AC_ROM_REG_SVA

bind rw_manager_ac_ROM_reg rw_manager_ac_ROM_reg_sva u_rw_manager_ac_ROM_reg_sva();

module rw_manager_ac_ROM_reg_sva;

  // helper to gate $past usage
  bit past_valid;
  always @(posedge clock) past_valid <= 1'b1;

  // Basic X/Z hygiene
  assert property (@(posedge clock) !$isunknown(wren))
    else $error("rw_manager_ac_ROM_reg: wren is X/Z");
  assert property (@(posedge clock) !$isunknown(rdaddress))
    else $error("rw_manager_ac_ROM_reg: rdaddress has X/Z");
  assert property (@(posedge clock) wren |-> !$isunknown({wraddress, data}))
    else $error("rw_manager_ac_ROM_reg: wraddress/data X/Z when wren");

  // Read-first, 1-cycle latency: q mirrors previous cycle's memory at previous rdaddress
  assert property (@(posedge clock) disable iff (!past_valid)
                   q == $past(ac_mem[$past(rdaddress)]))
    else $error("rw_manager_ac_ROM_reg: q mismatch vs prior mem[prior rdaddress]");

  // Write effect: a write updates the location by next cycle
  assert property (@(posedge clock) disable iff (!past_valid)
                   $past(wren) |-> ac_mem[$past(wraddress)] == $past(data))
    else $error("rw_manager_ac_ROM_reg: write did not update memory by next cycle");

  // No unintended q change when same address and no write to it in prior cycle
  assert property (@(posedge clock) disable iff (!past_valid)
                   (rdaddress == $past(rdaddress) &&
                    !($past(wren) && ($past(wraddress) == rdaddress)))
                   |-> q == $past(q))
    else $error("rw_manager_ac_ROM_reg: q changed without a write to its address");

  // Hazard-specific: same-cycle write/read to same address returns old data (read-first)
  assert property (@(posedge clock) disable iff (!past_valid)
                   $past(wren && (wraddress == rdaddress)) |-> q == $past(ac_mem[rdaddress],1))
    else $error("rw_manager_ac_ROM_reg: read-during-write not read-first");

  // Coverage
  cover property (@(posedge clock) wren);                                                // any write
  cover property (@(posedge clock) past_valid && rdaddress != $past(rdaddress));         // read addr change
  cover property (@(posedge clock) wren && (wraddress == rdaddress));                    // write/read same addr same cycle
  cover property (@(posedge clock) wren ##1 (rdaddress == $past(wraddress)));            // write then read that addr next cycle
  cover property (@(posedge clock) wren ##1 wren && (wraddress == $past(wraddress)));    // back-to-back writes same addr
  cover property (@(posedge clock)
                  wren ##1 (rdaddress == $past(wraddress)) ##1 (q == $past(data,2)));    // observe written data on q

endmodule

`endif
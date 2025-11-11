// SVA for avalon_to_wb_bridge
// Bind into the DUT to access internal regs (read_access, readdatavalid, readdata)
module avalon_to_wb_bridge_sva;

  // Use DUT scope signals directly via bind
  // Clock and reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic combinational mapping and constants
  assert property (
    (wbm_adr_o == avm_address_i) &&
    (wbm_sel_o == avm_byteenable_i) &&
    (wbm_dat_o == avm_writedata_i) &&
    (wbm_we_o  == avm_write_i)     &&
    (wbm_cyc_o == wbm_stb_o)       &&
    (wbm_cyc_o == (read_access || avm_write_i)) &&
    (wbm_cti_o == 3'b111) && (wbm_bte_o == 2'b00)
  );

  // Avalon waitrequest mirrors not(ack|err)
  assert property (avm_waitrequest_o == !(wbm_ack_i || wbm_err_i));

  // Read-data-valid exactly when (ack|err) and a read is in flight
  assert property (avm_readdatavalid_o == ((wbm_ack_i || wbm_err_i) && read_access));

  // Data returned when valid matches Wishbone return data
  assert property (avm_readdatavalid_o |-> (avm_readdata_o == wbm_dat_i));

  // Read-data-valid must not occur on a write
  assert property (avm_readdatavalid_o |-> !wbm_we_o);

  // Wishbone ack/err only with an active cycle
  assert property ((wbm_ack_i || wbm_err_i) |-> wbm_cyc_o);

  // Read FSM behavior: set/clear and priority vs ack/err
  // If a read is requested and no ack/err that cycle, read_access sets next cycle
  assert property ((avm_read_i && !(wbm_ack_i || wbm_err_i)) |=> read_access);
  // Ack/err has priority over avm_read_i (same-cycle clear)
  assert property ((wbm_ack_i || wbm_err_i) && avm_read_i |-> !read_access);
  // Any ack/err clears read_access
  assert property ((wbm_ack_i || wbm_err_i) |-> !read_access);

  // Do not allow a write while a read is outstanding (prevents readdatavalid on write acks)
  assert property ( (read_access && !(wbm_ack_i || wbm_err_i)) |-> (!avm_write_i until (wbm_ack_i || wbm_err_i)) );

  // Avalon master must hold request signals stable while stalled
  assert property (
    ((avm_read_i || avm_write_i) && avm_waitrequest_o) |->
      ($stable(avm_address_i)   &&
       $stable(avm_byteenable_i)&&
       $stable(avm_writedata_i) &&
       $stable(avm_write_i)     &&
       $stable(avm_read_i)) until (!avm_waitrequest_o)
  );

  // Bridge only supports single-beat (burstcount must be 1 when a request is issued)
  assert property ((avm_read_i || avm_write_i) |-> (avm_burstcount_i == 8'd1));

  // Coverage: exercise read, write, and error paths
  cover property (avm_read_i ##[1:$] avm_readdatavalid_o);
  cover property (avm_write_i ##[1:$] (wbm_ack_i || wbm_err_i));
  cover property (avm_read_i ##[1:$] (wbm_err_i && avm_readdatavalid_o));

endmodule

bind avalon_to_wb_bridge avalon_to_wb_bridge_sva;
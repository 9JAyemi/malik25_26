// SVA for niosii_nios2_gen2_0_cpu_nios2_oci_dtrace
// Focus: reset behavior, update conditions, precedence, stability, wiring, and coverage.

module niosii_nios2_gen2_0_cpu_nios2_oci_dtrace_sva;

  // Use DUT scope via bind; no ports
  default clocking cb @(posedge clk); endclocking
  default disable iff (!jrst_n);

  // 1) Asynchronous reset drives zeros
  // Immediate check at negedge of async reset
  always @(negedge jrst_n) begin
    assert (atm == 32'h0 && dtm == 32'h0);
  end
  // Also hold-zero while in reset
  assert property ( !jrst_n |-> (atm == 32'h0 && dtm == 32'h0) );

  // 2) Combinational/wiring checks
  // td_mode extraction and mapping to record_* enables
  assert property ( {record_load_addr, record_store_addr, record_load_data, record_store_data} == trc_ctrl[3:0] );
  // Padded bus wiring sanity
  assert property ( cpu_d_readdata_0_padded == cpu_d_readdata );
  assert property ( cpu_d_writedata_0_padded == cpu_d_writedata );
  assert property ( cpu_d_address_0_padded[22:0] == cpu_d_address
                 && cpu_d_address_0_padded[31:23] == '0 );

  // 3) Output updates occur only when allowed, with correct values
  // atm only updates on addr record for read/write when not waiting
  assert property (
    $changed(atm) |->
      (!cpu_d_wait) &&
      (
        (cpu_d_read  && record_load_addr  && atm == cpu_d_address_0_padded) ||
        (!cpu_d_read && cpu_d_write && record_store_addr && atm == cpu_d_address_0_padded)
      )
  );

  // dtm only updates on data record for read/write when not waiting
  // Read has priority over write when both asserted
  assert property (
    $changed(dtm) |->
      (!cpu_d_wait) &&
      (
        (cpu_d_read && record_load_data && dtm == cpu_d_readdata_0_padded) ||
        (!cpu_d_read && cpu_d_write && record_store_data && dtm == cpu_d_writedata_0_padded)
      )
  );

  // 4) Precedence checks (read takes priority over write)
  assert property (
    (!cpu_d_wait && cpu_d_read && record_load_addr) |-> (atm == cpu_d_address_0_padded)
  );
  assert property (
    (!cpu_d_wait && cpu_d_read && record_load_data) |-> (dtm == cpu_d_readdata_0_padded)
  );

  // 5) Stability when no update should occur
  // Under wait, nothing changes
  assert property ( cpu_d_wait |-> ($stable(atm) && $stable(dtm)) );

  // During read with no addr/data record, respective output holds
  assert property ( (!cpu_d_wait && cpu_d_read  && !record_load_addr)  |-> $stable(atm) );
  assert property ( (!cpu_d_wait && cpu_d_read  && !record_load_data)  |-> $stable(dtm) );

  // During write with no addr/data record, respective output holds
  assert property ( (!cpu_d_wait && !cpu_d_read && cpu_d_write && !record_store_addr) |-> $stable(atm) );
  assert property ( (!cpu_d_wait && !cpu_d_read && cpu_d_write && !record_store_data) |-> $stable(dtm) );

  // 6) Functional coverage (one-shot hits for each record path and precedence)
  cover property ( !cpu_d_wait && cpu_d_read  && record_load_addr  ##0 $changed(atm) );
  cover property ( !cpu_d_wait && cpu_d_write && record_store_addr ##0 $changed(atm) );
  cover property ( !cpu_d_wait && cpu_d_read  && record_load_data  ##0 $changed(dtm) );
  cover property ( !cpu_d_wait && cpu_d_write && record_store_data ##0 $changed(dtm) );

  // Cover read-over-write precedence on same cycle when both asserted and both data/addr enabled
  cover property ( !cpu_d_wait && cpu_d_read && cpu_d_write &&
                   record_load_addr && record_store_addr &&
                   record_load_data && record_store_data );

  // Cover reset then first capture after coming out of reset
  cover property ( !jrst_n ##1 jrst_n ##[1:10] (!cpu_d_wait && (cpu_d_read || cpu_d_write)) );

endmodule

bind niosii_nios2_gen2_0_cpu_nios2_oci_dtrace niosii_nios2_gen2_0_cpu_nios2_oci_dtrace_sva sva_i;
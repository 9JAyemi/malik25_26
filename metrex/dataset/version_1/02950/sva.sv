// SVA for dual_port_ram
// Bind this file to the DUT: bind dual_port_ram dual_port_ram_sva sva();

// Notes:
// - Treat multi-bit enables as boolean: (en != 0)

module dual_port_ram_sva;

  // These names resolve inside the bound dual_port_ram instance
  // (clk, rst_n, mem, write_en_*, write_addr_*, write_data_*, read_en_*, read_addr_*, read_data_*)

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity: no X/Z on controls/addresses, data valid when writing
  ap_no_x_ctrl: assert property (!$isunknown({write_en_0, read_en_0, write_en_1, read_en_1,
                                             write_addr_0, write_addr_1, read_addr_0, read_addr_1}));
  ap_no_x_wd0:   assert property ((write_en_0!=0) |-> !$isunknown(write_data_0));
  ap_no_x_wd1:   assert property ((write_en_1!=0) |-> !$isunknown(write_data_1));

  // Async reset drives outputs to 0 (checked on next clk after rst_n falls)
  ap_reset_clears_outs: assert property ($fell(rst_n) |=> (read_data_0==16'h0 && read_data_1==16'h0));

  // Outputs change only when respective read enable asserted
  ap_rd0_stable_no_en: assert property ((read_en_0==0) |-> $stable(read_data_0));
  ap_rd1_stable_no_en: assert property ((read_en_1==0) |-> $stable(read_data_1));

  // Read data = prior-cycle memory at prior address (old data on same-cycle write)
  ap_r0_data_old: assert property ((read_en_0!=0) |=> read_data_0 == $past(mem[$past(read_addr_0)]));
  ap_r1_data_old: assert property ((read_en_1!=0) |=> read_data_1 == $past(mem[$past(read_addr_1)]));

  // Write semantics:
  // - Port1 always takes effect on its address
  ap_w1_updates: assert property ((write_en_1!=0) |=> mem[$past(write_addr_1)] == $past(write_data_1));

  // - Port0 takes effect unless Port1 overwrites same address
  ap_w0_updates: assert property (((write_en_0!=0) && !((write_en_1!=0) && (write_addr_1==write_addr_0)))
                                  |=> mem[$past(write_addr_0)] == $past(write_data_0));

  // - Collision resolution: if both write same addr, Port1 wins
  ap_collision_order: assert property (((write_en_0!=0) && (write_en_1!=0) && (write_addr_0==write_addr_1))
                                       |=> mem[$past(write_addr_0)] == $past(write_data_1));

  // Optional: outputs never X after reset released
  ap_rd0_never_x: assert property (!$isunknown(read_data_0));
  ap_rd1_never_x: assert property (!$isunknown(read_data_1));

  // Coverage: key scenarios
  cv_two_writes_diff_addr: cover property ((write_en_0!=0) && (write_en_1!=0) && (write_addr_0!=write_addr_1));
  cv_two_writes_same_addr: cover property ((write_en_0!=0) && (write_en_1!=0) && (write_addr_0==write_addr_1));
  cv_read_during_write_same_addr_0w0r: cover property ((write_en_0!=0) && (read_en_0!=0) && (write_addr_0==read_addr_0));
  cv_read_during_write_same_addr_1w0r: cover property ((write_en_1!=0) && (read_en_0!=0) && (write_addr_1==read_addr_0));
  cv_read_during_write_same_addr_0w1r: cover property ((write_en_0!=0) && (read_en_1!=0) && (write_addr_0==read_addr_1));
  cv_read_during_write_same_addr_1w1r: cover property ((write_en_1!=0) && (read_en_1!=0) && (write_addr_1==read_addr_1));
  cv_both_reads:                cover property ((read_en_0!=0) && (read_en_1!=0));
  cv_wr0_then_rd0:             cover property ((write_en_0!=0) ##1 (read_en_0!=0 && read_addr_0==$past(write_addr_0)));
  cv_wr1_then_rd1:             cover property ((write_en_1!=0) ##1 (read_en_1!=0 && read_addr_1==$past(write_addr_1)));

endmodule

bind dual_port_ram dual_port_ram_sva sva();
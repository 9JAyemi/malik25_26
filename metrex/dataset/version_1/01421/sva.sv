// SVA checker for vga_core
// Bind this module to the DUT: bind vga_core vga_core_sva u_vga_core_sva();

module vga_core_sva (vga_core dut);

  // Clocking
  default clocking cb @(posedge dut.vga_clk); endclocking

  // Reset behavior (checked during reset)
  ap_reset_counts: assert property (@(posedge dut.vga_clk)
    dut.rst |-> (dut.h_count==10'd0 && dut.v_count==10'd0));

  // Disable assertions while in reset
  default disable iff (dut.rst);

  // Counter ranges
  ap_hcount_range: assert property (dut.h_count <= 10'd799);
  ap_vcount_range: assert property (dut.v_count <= 10'd524);

  // h_count step and wrap
  ap_hcount_inc:  assert property ($past(!dut.rst) && $past(dut.h_count) < 10'd799 |-> dut.h_count == $past(dut.h_count)+10'd1);
  ap_hcount_wrap: assert property ($past(!dut.rst) && $past(dut.h_count) == 10'd799 |-> dut.h_count == 10'd0);

  // v_count hold, step and wrap (only advances on h_count wrap)
  ap_vcount_hold: assert property ($past(!dut.rst) && $past(dut.h_count) != 10'd799 |-> dut.v_count == $past(dut.v_count));
  ap_vcount_inc:  assert property ($past(!dut.rst) && $past(dut.h_count)==10'd799 && $past(dut.v_count) < 10'd524 |-> dut.v_count == $past(dut.v_count)+10'd1);
  ap_vcount_wrap: assert property ($past(!dut.rst) && $past(dut.h_count)==10'd799 && $past(dut.v_count) == 10'd524 |-> dut.v_count == 10'd0);

  // Combinational timing signals match definitions
  ap_hsync_def:   assert property (dut.h_sync == (dut.h_count > 10'd95));
  ap_vsync_def:   assert property (dut.v_sync == (dut.v_count > 10'd1));
  ap_vactive_def: assert property (dut.v_active ==
                                  ((dut.h_count > 10'd142) && (dut.h_count < 10'd783) &&
                                   (dut.v_count > 10'd34)  && (dut.v_count < 10'd515)));

  // Active implies syncs high
  ap_active_syncs_high: assert property (dut.v_active |-> (dut.h_sync && dut.v_sync));

  // Address mapping when active: {row[8:0], col[9:0]} = {v_count-35, h_count-143}
  ap_addr_map_when_active: assert property (
    dut.v_active |-> (dut.addr[9:0]   == (dut.h_count - 10'd143)) &&
                     (dut.addr[18:10] == (dut.v_count - 10'd35)[8:0])
  );

  // Address bounds when active
  ap_addr_bounds_when_active: assert property (
    dut.v_active |-> (dut.addr[9:0] <= 10'd639) && (dut.addr[18:10] <= 9'd479)
  );

  // Horizontal address increments by 1 within active line (except at last active column)
  ap_addr_inc_horiz: assert property (
    dut.v_active && (dut.h_count < 10'd782) |=> (dut.v_active && dut.addr == $past(dut.addr)+19'd1)
  );

  // Edge checks at active window boundaries
  ap_first_col_addr0:  assert property (dut.v_active && dut.h_count==10'd143 |-> dut.addr[9:0]==10'd0);
  ap_last_col_addr639: assert property (dut.v_active && dut.h_count==10'd782 |-> dut.addr[9:0]==10'd639);
  ap_first_row_row0:   assert property (dut.v_active && dut.v_count==10'd35  |-> dut.addr[18:10]==9'd0);
  ap_last_row_row479:  assert property (dut.v_active && dut.v_count==10'd514 |-> dut.addr[18:10]==9'd479);

  // Coverage: key events
  cv_hcount_wrap:   cover property (dut.h_count==10'd799 ##1 dut.h_count==10'd0);
  cv_vcount_wrap:   cover property ((dut.h_count==10'd799 && dut.v_count==10'd524) ##1 (dut.h_count==10'd0 && dut.v_count==10'd0));
  cv_active_start:  cover property (dut.v_active && dut.h_count==10'd143 && dut.v_count==10'd35);
  cv_active_end:    cover property (dut.v_active && dut.h_count==10'd782 && dut.v_count==10'd514);
  cv_hsync_edge:    cover property (dut.h_count==10'd95 && !dut.h_sync ##1 dut.h_count==10'd96 && dut.h_sync);
  cv_vsync_edge:    cover property (dut.v_count==10'd1  && !dut.v_sync ##1 dut.v_count==10'd2  && dut.v_sync);
  cv_addr_inc:      cover property (dut.v_active && dut.h_count==10'd144 && dut.addr == $past(dut.addr)+19'd1);

endmodule

// Example bind (place in a testbench or package):
// bind vga_core vga_core_sva u_vga_core_sva();
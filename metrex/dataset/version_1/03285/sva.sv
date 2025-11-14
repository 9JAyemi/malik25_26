// SVA for MIB_DDR_SDRAM
`ifndef MIB_DDR_SDRAM_SVA
`define MIB_DDR_SDRAM_SVA

module MIB_DDR_SDRAM_sva #(
  parameter DATA_WIDTH = 32,
  parameter ADDR_WIDTH = 8
) ();
  // This module is intended to be bound into MIB_DDR_SDRAM; it directly references its signals/mem.
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset behavior
  a_async_rst_now:     assert property (@(posedge rst) dout == '0);
  a_rst_holds_zero:    assert property (@(posedge clk) rst |-> dout == '0);

  // X/Z checks when active
  a_no_x_we_addr:      assert property (disable iff (rst) !$isunknown(we) && !$isunknown(addr));
  a_no_x_din_on_write: assert property (disable iff (rst) we |-> !$isunknown(din));

  // Functional correctness
  // Write updates only the targeted element (checked at next clk)
  a_write_updates_mem: assert property (disable iff (rst)
                                        we |-> ##1 mem[$past(addr)] == $past(din));

  // Read updates dout with prior memory content at that address (checked at next clk)
  a_read_updates_dout: assert property (disable iff (rst)
                                        !we |-> ##1 dout == $past(mem[$past(addr)]));

  // Writes do not modify dout
  a_write_keeps_dout:  assert property (disable iff (rst)
                                        we |-> ##1 dout == $past(dout));

  // Minimal functional coverage
  c_write:                 cover property (disable iff (rst) we);
  c_read:                  cover property (disable iff (rst) !we);
  c_w_then_r_same_addr:    cover property (disable iff (rst)
                                           we ##1 (!we && addr == $past(addr) && dout == $past(din)));
  c_access_max_addr_write: cover property (disable iff (rst) we   && addr == {ADDR_WIDTH{1'b1}});
  c_access_max_addr_read:  cover property (disable iff (rst) !we  && addr == {ADDR_WIDTH{1'b1}});
endmodule

bind MIB_DDR_SDRAM MIB_DDR_SDRAM_sva #(.DATA_WIDTH(DATA_WIDTH), .ADDR_WIDTH(ADDR_WIDTH)) i_MIB_DDR_SDRAM_sva();

`endif
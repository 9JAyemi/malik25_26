// SVA for reg_32bits
module reg_32bits_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        we,
  input  logic [31:0] d,
  input  logic [31:0] q
);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset clears output immediately (post-NBA)
  a_async_clear_immediate: assert property (@(posedge rst) ##0 (q == 32'h0));

  // While reset is asserted, q must be zero at every clock
  a_rst_forces_zero:       assert property (rst |-> (q == 32'h0));

  // Synchronous write: capture d on next clock when we and not in reset
  a_write_updates_q:       assert property (disable iff (rst) we |=> (q == $past(d)));

  // Hold value when not writing (and not in reset)
  a_hold_on_no_write:      assert property (disable iff (rst) !we |=> (q == $past(q)));

  // q may only change (between clocks) due to a write; ignore async reset effects
  a_change_only_on_we:     assert property ((!rst && !$rose(rst) && (q != $past(q))) |-> $past(we));

  // After reset deasserts, hold zero until the first write
  a_hold_zero_until_we:    assert property ($fell(rst) |-> (q == 32'h0 until (we && !rst)));

  // Coverage
  c_rst_assert:            cover  property (@(posedge rst) 1);
  c_rst_deassert:          cover  property ($fell(rst));
  c_single_write:          cover  property (disable iff (rst) we);
  c_back_to_back_writes:   cover  property (disable iff (rst) we ##1 we);
  c_write_zero:            cover  property (disable iff (rst) we && d == 32'h0000_0000);
  c_write_ones:            cover  property (disable iff (rst) we && d == 32'hFFFF_FFFF);
  c_write_after_release:   cover  property ($fell(rst) ##1 we);
endmodule

// Bind into DUT
bind reg_32bits reg_32bits_sva u_reg_32bits_sva (.clk(clk), .rst(rst), .we(we), .d(d), .q(q));
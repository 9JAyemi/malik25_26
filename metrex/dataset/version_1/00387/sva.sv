// SVA for system_auto_cc_0_synchronizer_ff__parameterized2
// Checks async-clear, 1-cycle capture, X-safety, and basic coverage.

module system_auto_cc_0_synchronizer_ff__parameterized2_sva (
  input  logic        s_aclk,
  input  logic [0:0]  ngwrdrst_grst_g7serrst_rd_rst_reg_reg_1,
  input  logic [3:0]  Q_reg_reg_0,
  input  logic [3:0]  D
);
  wire rst = ngwrdrst_grst_g7serrst_rd_rst_reg_reg_1[0];

  default clocking cb @(posedge s_aclk); endclocking

  // Reset known at clock edges
  a_rst_known:            assert property (@cb !$isunknown(rst));

  // Output known when not in reset
  a_no_x_on_D:            assert property (@cb disable iff (rst) !$isunknown(D));

  // Async clear immediate effect
  always @(posedge rst) begin
    a_async_clear_immediate: assert (D == '0);
    c_async_clear_seen:      cover  (1);
  end

  // Hold zero while reset is asserted (synchronous check)
  a_hold_zero_in_rst:      assert property (@cb rst |-> D == '0);

  // 1-cycle capture when not in reset
  a_sync_capture:          assert property (@cb disable iff (rst) D == $past(Q_reg_reg_0));

  // First non-reset clock after deassert captures input
  a_cap_after_rst_fall:    assert property (@cb $fell(rst) |-> D == $past(Q_reg_reg_0));

  // Bit-level toggle coverage out of reset
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : g_cov
      c_rose_D: cover property (@cb disable iff (rst) $rose(D[i]));
      c_fell_D: cover property (@cb disable iff (rst) $fell(D[i]));
    end
  endgenerate

  // Reset assert/deassert coverage
  c_rst_assert:            cover property (@cb $rose(rst));
  c_rst_deassert:          cover property (@cb $fell(rst));

endmodule

bind system_auto_cc_0_synchronizer_ff__parameterized2
  system_auto_cc_0_synchronizer_ff__parameterized2_sva
  (.s_aclk(s_aclk),
   .ngwrdrst_grst_g7serrst_rd_rst_reg_reg_1(ngwrdrst_grst_g7serrst_rd_rst_reg_reg_1),
   .Q_reg_reg_0(Q_reg_reg_0),
   .D(D));
// SVA for system_control
// Focused, concise checks + key coverage
module system_control_sva
(
  input logic        wb_clk_i,
  input logic        ram_loader_done_i,
  input logic        ram_loader_rst_o,
  input logic        wb_rst_o,
  input logic        POR,
  input logic [3:0]  POR_ctr,
  input logic        delayed_rst
);

  default clocking cb @(posedge wb_clk_i); endclocking

  // Guard $past on first cycle
  logic past_valid; initial past_valid = 1'b0;
  always @(posedge wb_clk_i) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // POR generation/CTR
  A_POR_never_reassert:       assert property (!$rose(POR));
  A_POR_falls_when_ctr_15:    assert property ($fell(POR) |-> $past(POR_ctr) == 4'd15);
  A_CTR_freeze_after_POR:     assert property (!POR |-> (POR_ctr == 4'd15 && $stable(POR_ctr)));

  // ram_loader_rst_o behavior
  A_RLRST_while_POR:          assert property (POR |->  ram_loader_rst_o);
  A_RLRST_drop_next:          assert property ($fell(POR) |=> !ram_loader_rst_o);
  A_RLRST_no_reassert:        assert property ($fell(ram_loader_rst_o) |-> !POR);
  A_RLRST_stable_low:         assert property ((!POR && !ram_loader_rst_o) |-> $stable(ram_loader_rst_o));

  // wb_rst_o behavior (requires two consecutive 'done' cycles to drop)
  A_WBRST_while_POR:          assert property (POR |-> wb_rst_o);
  A_WBRST_hold_until_2done:   assert property ((!POR) |-> (wb_rst_o until_with (ram_loader_done_i[*2])));
  A_WBRST_drop_after_2done:   assert property ((!POR && ram_loader_done_i && $past(ram_loader_done_i)) |=> !wb_rst_o);
  A_WBRST_fall_implies_2done: assert property ($fell(wb_rst_o) |-> $past(ram_loader_done_i) && $past(ram_loader_done_i,2));

  // delayed_rst behavior
  A_DLYRST_while_POR:         assert property (POR |-> delayed_rst);
  A_DLYRST_drop_on_done:      assert property ((!POR && ram_loader_done_i) |=> !delayed_rst);
  A_DLYRST_sticky_low:        assert property ((!POR && !delayed_rst) |-> $stable(delayed_rst));

  // Basic X-check
  A_No_X:                     assert property (!$isunknown({ram_loader_rst_o, wb_rst_o, delayed_rst, POR, POR_ctr}));

  // Key functional coverage
  C_Reset_release_flow:       cover property ($fell(POR) ##1 (!ram_loader_rst_o && wb_rst_o)
                                              ##1 (ram_loader_done_i && !POR)
                                              ##1 (ram_loader_done_i)
                                              ##1 (!wb_rst_o));

  C_Single_done_no_release:   cover property ($fell(POR) ##1 wb_rst_o ##1 (ram_loader_done_i && !POR)
                                              ##1 (!ram_loader_done_i) ##1 wb_rst_o);

endmodule

// Bind into DUT (grabs internal regs via .*)
bind system_control system_control_sva i_system_control_sva (.*);
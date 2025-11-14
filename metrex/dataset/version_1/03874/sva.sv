// SVA for mig_7series_v4_0_axi_mc_wr_cmd_fsm
// Synthesis off
`ifndef MIG_7SERIES_V4_0_AXI_MC_WR_CMD_FSM_SVA
`define MIG_7SERIES_V4_0_AXI_MC_WR_CMD_FSM_SVA

module mig_7series_v4_0_axi_mc_wr_cmd_fsm_sva #(
  parameter int C_MC_BURST_LEN = 1,
  parameter int C_MC_RD_INST   = 0
)(
  input  logic clk,
  input  logic reset,
  input  logic axvalid,
  input  logic cmd_full,
  input  logic next_pending,
  input  logic data_rdy,
  input  logic b_full,
  input  logic axready,
  input  logic cmd_en,
  input  logic next,
  input  logic b_push,
  input  logic cmd_en_last
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Functional equalities (combinational outputs)
  ap_cmd_en_def:       assert property (cmd_en      == (~b_full & axvalid & data_rdy));
  ap_next_def:         assert property (next        == (~cmd_full & cmd_en));
  ap_cmd_en_last_def:  assert property (cmd_en_last == (next & ~next_pending));
  ap_b_push_def:       assert property (b_push      == cmd_en_last);

  // Registered axready behavior
  ap_axready_reset:    assert property (@(posedge clk) reset |-> (axready == 1'b0));
  ap_axready_def:      assert property (axready == (~axvalid | cmd_en_last));

  // Helpful implications (redundant but diagnostic)
  ap_cmd_en_imp:       assert property (cmd_en      |-> (axvalid && data_rdy && !b_full));
  ap_next_imp:         assert property (next        |-> (!cmd_full && cmd_en));
  ap_cmd_en_last_imp:  assert property (cmd_en_last |-> (next && !next_pending));
  ap_b_push_imp:       assert property (b_push      |-> cmd_en_last);

  // Outputs should not be X/Z post-reset
  ap_no_x_out:         assert property (!$isunknown({cmd_en,next,cmd_en_last,b_push,axready}));

  // Coverage: key scenarios
  cp_full_issue:           cover property (axvalid && data_rdy && !b_full && !cmd_full && !next_pending &&
                                           cmd_en && next && cmd_en_last && b_push);
  cp_b_full_blocks:        cover property (axvalid && data_rdy &&  b_full && !cmd_en);
  cp_cmd_full_blocks:      cover property (cmd_en && cmd_full && !next);
  cp_next_pending_blocks:  cover property (next && next_pending && !cmd_en_last && !b_push);
  cp_axready_idle:         cover property (!axvalid && axready);
  cp_axready_with_issue:   cover property (axvalid && cmd_en_last && axready);

endmodule

// Bind into DUT
bind mig_7series_v4_0_axi_mc_wr_cmd_fsm
  mig_7series_v4_0_axi_mc_wr_cmd_fsm_sva #(
    .C_MC_BURST_LEN(C_MC_BURST_LEN),
    .C_MC_RD_INST  (C_MC_RD_INST)
  ) sva_i (
    .clk(clk),
    .reset(reset),
    .axvalid(axvalid),
    .cmd_full(cmd_full),
    .next_pending(next_pending),
    .data_rdy(data_rdy),
    .b_full(b_full),
    .axready(axready),
    .cmd_en(cmd_en),
    .next(next),
    .b_push(b_push),
    .cmd_en_last(cmd_en_last)
  );

`endif
// Synthesis on
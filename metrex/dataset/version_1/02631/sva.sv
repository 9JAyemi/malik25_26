// SVA for PIO_TO_CTRL
// Bind this file to the DUT

module pio_to_ctrl_sva (
  input  logic clk,
  input  logic rst_n,
  input  logic req_compl_i,
  input  logic compl_done_i,
  input  logic cfg_to_turnoff,
  input  logic trn_pending,
  input  logic cfg_turnoff_ok
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // X/known checks
  a_xcheck: assert property (!$isunknown({req_compl_i, compl_done_i, cfg_to_turnoff, trn_pending, cfg_turnoff_ok}));

  // Asynchronous reset drives regs low on falling edge of rst_n
  a_reset_vals: assert property (disable iff (1'b0)
                                 @(posedge clk) $fell(rst_n) |-> (trn_pending==1'b0 && cfg_turnoff_ok==1'b0));

  // trn_pending next-state semantics
  a_set_when_req_idle: assert property ((!trn_pending && req_compl_i) |=> trn_pending);
  a_hold_idle_no_req:  assert property ((!trn_pending && !req_compl_i) |=> !trn_pending);
  a_clear_on_done:     assert property ((trn_pending && compl_done_i) |=> !trn_pending);
  a_hold_busy_no_done: assert property ((trn_pending && !compl_done_i) |=> trn_pending);

  // Edges imply legal causes
  a_rise_cause:        assert property ($rose(trn_pending) |-> (!$past(trn_pending) && req_compl_i));
  a_fall_cause:        assert property ($fell(trn_pending) |-> compl_done_i);

  // Priority when both req and done in same cycle while idle => set
  a_req_done_same_cycle_priority: assert property ((!trn_pending && req_compl_i && compl_done_i) |=> trn_pending);

  // cfg_turnoff_ok must reflect cfg_to_turnoff && !trn_pending (registered same-cycle)
  a_cfg_ok_equiv:      assert property (cfg_turnoff_ok == (cfg_to_turnoff && !trn_pending));

  // Functional coverage
  c_req_done_cycle:    cover property (!trn_pending ##1 req_compl_i ##1 trn_pending ##[1:$] compl_done_i ##1 !trn_pending);
  c_turnoff_grant:     cover property ((cfg_to_turnoff && !trn_pending) ##1 cfg_turnoff_ok);
  c_turnoff_block_then_grant:
                       cover property (trn_pending ##1 cfg_to_turnoff ##[1:$] compl_done_i ##1 cfg_turnoff_ok);
  c_req_and_done_same: cover property ((!trn_pending && req_compl_i && compl_done_i) ##1 trn_pending);

endmodule

bind PIO_TO_CTRL pio_to_ctrl_sva
  pio_to_ctrl_sva_i (
    .clk           (clk),
    .rst_n         (rst_n),
    .req_compl_i   (req_compl_i),
    .compl_done_i  (compl_done_i),
    .cfg_to_turnoff(cfg_to_turnoff),
    .trn_pending   (trn_pending),
    .cfg_turnoff_ok(cfg_turnoff_ok)
  );
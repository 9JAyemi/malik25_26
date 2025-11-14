// SVA for PIO_TO_CTRL
module PIO_TO_CTRL_sva (
  input  logic clk,
  input  logic rst_n,
  input  logic req_compl_i,
  input  logic compl_done_i,
  input  logic cfg_to_turnoff_n,
  input  logic cfg_turnoff_ok_n,
  input  logic trn_pending
);

  // Reset values
  ap_reset_vals: assert property (@(posedge clk) !rst_n |-> (trn_pending==1'b0 && cfg_turnoff_ok_n==1'b1));

  // No X on stateful/internal outputs after reset
  ap_no_x: assert property (@(posedge clk) disable iff (!rst_n) !$isunknown({trn_pending, cfg_turnoff_ok_n}));

  // Combinational relation encoded by RTL: cfg_turnoff_ok_n == (cfg_to_turnoff_n || trn_pending)
  ap_cfg_expr: assert property (@(posedge clk) disable iff (!rst_n)
                                cfg_turnoff_ok_n == (cfg_to_turnoff_n || trn_pending));

  // Next-state rules for trn_pending
  ap_set_pending:   assert property (@(posedge clk) disable iff (!rst_n)
                                     (!trn_pending && req_compl_i) |=> trn_pending);
  ap_clear_pending: assert property (@(posedge clk) disable iff (!rst_n)
                                     (trn_pending && compl_done_i) |=> !trn_pending);

  // No spurious transitions
  ap_no_spurious_set:   assert property (@(posedge clk) disable iff (!rst_n)
                                         $rose(trn_pending) |-> $past(!trn_pending && req_compl_i));
  ap_no_spurious_clear: assert property (@(posedge clk) disable iff (!rst_n)
                                         $fell(trn_pending) |-> $past(compl_done_i));
  ap_hold_when_busy_no_done: assert property (@(posedge clk) disable iff (!rst_n)
                                              (trn_pending && !compl_done_i) |=> trn_pending);
  ap_hold_when_idle_no_req:  assert property (@(posedge clk) disable iff (!rst_n)
                                              (!trn_pending && !req_compl_i) |=> !trn_pending);

  // Output polarity checks (redundant with ap_cfg_expr but useful for debug intent)
  ap_okn_low_if:  assert property (@(posedge clk) disable iff (!rst_n)
                                   (cfg_turnoff_ok_n==1'b0) |-> (!cfg_to_turnoff_n && !trn_pending));
  ap_okn_high_if: assert property (@(posedge clk) disable iff (!rst_n)
                                   (cfg_turnoff_ok_n==1'b1) |-> (cfg_to_turnoff_n || trn_pending));

  // Coverage
  cp_req_then_done: cover property (@(posedge clk) disable iff (!rst_n)
                                    (!trn_pending && req_compl_i) ##1 trn_pending
                                    ##[1:$] (compl_done_i && trn_pending) ##1 !trn_pending);

  // Both-high corner cases
  cp_both_high_idle_sets: cover property (@(posedge clk) disable iff (!rst_n)
                                          (!trn_pending && req_compl_i && compl_done_i) ##1 trn_pending);
  cp_both_high_busy_clears: cover property (@(posedge clk) disable iff (!rst_n)
                                            (trn_pending && req_compl_i && compl_done_i) ##1 !trn_pending);

  // Turnoff handshake coverage
  cp_okn_goes_low: cover property (@(posedge clk) disable iff (!rst_n)
                                   (!cfg_to_turnoff_n && !trn_pending) ##1 (cfg_turnoff_ok_n==1'b0));
  cp_turnoff_blocked_when_pending: cover property (@(posedge clk) disable iff (!rst_n)
                                                   (!cfg_to_turnoff_n && trn_pending && cfg_turnoff_ok_n));

endmodule

// Bind into DUT (connects to internal trn_pending and registered output)
bind PIO_TO_CTRL PIO_TO_CTRL_sva u_PIO_TO_CTRL_sva (
  .clk               (clk),
  .rst_n             (rst_n),
  .req_compl_i       (req_compl_i),
  .compl_done_i      (compl_done_i),
  .cfg_to_turnoff_n  (cfg_to_turnoff_n),
  .cfg_turnoff_ok_n  (cfg_turnoff_ok_n),
  .trn_pending       (trn_pending)
);
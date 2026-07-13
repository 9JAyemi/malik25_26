module PIO_TO_CTRL_sva (
    input logic clk,
    input logic rst_n,
    input logic req_compl_i,
    input logic compl_done_i,
    input logic cfg_to_turnoff,
    input logic cfg_turnoff_ok,
    input logic trn_pending
);

    // trn_pending is cleared while reset is active.
    check_trn_pending_reset: assert property (
        @(posedge clk) !rst_n |-> (trn_pending == 1'b0)
    );

    // cfg_turnoff_ok is cleared while reset is active.
    check_cfg_turnoff_ok_reset: assert property (
        @(posedge clk) !rst_n |-> (cfg_turnoff_ok == 1'b0)
    );

    // A request sets trn_pending on the next cycle when no transaction is pending.
    check_trn_pending_set_on_request: assert property (
        @(posedge clk) disable iff (!rst_n)
        (!trn_pending && req_compl_i) |=> (trn_pending == 1'b1)
    );

    // trn_pending stays low without a request when already idle.
    check_trn_pending_stays_low_without_request: assert property (
        @(posedge clk) disable iff (!rst_n)
        (!trn_pending && !req_compl_i) |=> (trn_pending == 1'b0)
    );

    // compl_done_i clears trn_pending on the next cycle when a transaction is pending.
    check_trn_pending_clear_on_completion: assert property (
        @(posedge clk) disable iff (!rst_n)
        (trn_pending && compl_done_i) |=> (trn_pending == 1'b0)
    );

    // trn_pending stays high until compl_done_i is asserted.
    check_trn_pending_hold_while_waiting: assert property (
        @(posedge clk) disable iff (!rst_n)
        (trn_pending && !compl_done_i) |=> (trn_pending == 1'b1)
    );

    // Turnoff is acknowledged on the next cycle when requested with no pending transaction.
    check_turnoff_ok_when_requested_and_idle: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cfg_to_turnoff && !trn_pending) |=> (cfg_turnoff_ok == 1'b1)
    );

    // Without a turnoff request, cfg_turnoff_ok is low on the next cycle.
    check_turnoff_ok_low_without_request: assert property (
        @(posedge clk) disable iff (!rst_n)
        (!cfg_to_turnoff) |=> (cfg_turnoff_ok == 1'b0)
    );

    // A pending transaction blocks turnoff acknowledgment.
    check_turnoff_ok_blocked_by_pending: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cfg_to_turnoff && trn_pending) |=> (cfg_turnoff_ok == 1'b0)
    );

endmodule
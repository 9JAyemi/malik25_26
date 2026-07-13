module d_ff_with_sync_clr_sva (
    input logic Clk,
    input logic D,
    input logic Q,
    input logic Clr
);

    // Q reflects the previous cycle's clear-or-data selection.
    check_transfer_function: assert property (
        @(posedge Clk) disable iff (1'b0)
        1'b1 |=> (Q == ($past(Clr) ? 1'b0 : $past(D)))
    );

    // A high clear forces Q low on the next sampled clock.
    check_sync_clear: assert property (
        @(posedge Clk) disable iff (1'b0)
        Clr |=> (Q == 1'b0)
    );

    // With clear low, Q captures D on the next sampled clock.
    check_data_capture: assert property (
        @(posedge Clk) disable iff (1'b0)
        !Clr |=> (Q == $past(D))
    );

    // Clear has priority over a high D input.
    check_clear_priority: assert property (
        @(posedge Clk) disable iff (1'b0)
        (Clr && D) |=> (Q == 1'b0)
    );

endmodule
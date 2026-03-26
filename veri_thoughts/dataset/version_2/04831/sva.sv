module d_ff_async_reset_sync_set_sva (
    input logic D,
    input logic C,
    input logic R,
    input logic E,
    input logic Q
);

    // Enabled clock edges update Q from the reset/data selection.
    check_enabled_update: assert property (
        @(posedge C) disable iff (1'b0)
        E |=> (Q == ($past(R) ? 1'b0 : $past(D)))
    );

    // Disabled clock edges hold the previous Q value.
    check_hold_when_disabled: assert property (
        @(posedge C) disable iff (1'b0)
        !E |=> (Q == $past(Q))
    );

    // Synchronous reset clears Q when E is high.
    check_sync_reset_clears_q: assert property (
        @(posedge C) disable iff (1'b0)
        (E && R) |=> (Q == 1'b0)
    );

    // With E high and no reset, D=1 is captured into Q.
    check_capture_one_when_enabled: assert property (
        @(posedge C) disable iff (1'b0)
        (E && !R && D) |=> (Q == 1'b1)
    );

    // With E high and no reset, D=0 is captured into Q.
    check_capture_zero_when_enabled: assert property (
        @(posedge C) disable iff (1'b0)
        (E && !R && !D) |=> (Q == 1'b0)
    );

    // E low prevents reset from changing Q on that clock edge.
    check_disabled_overrides_reset: assert property (
        @(posedge C) disable iff (1'b0)
        (!E && R) |=> (Q == $past(Q))
    );

endmodule
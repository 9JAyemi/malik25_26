module RegisterAdd__parameterized5_sva #(
    parameter int N = 23
) (
    input logic [N-1:0] Q,
    input logic [0:0]   E,
    input logic [N-1:0] D,
    input logic         CLK,
    input logic [0:0]   AR
);

    // Active-low reset clears the register.
    check_reset_clears_q: assert property (
        @(posedge CLK) !AR |-> (Q == {N{1'b0}})
    );

    // Reset overrides an enabled add.
    check_reset_priority_over_add: assert property (
        @(posedge CLK) (!AR && E) |-> (Q == {N{1'b0}})
    );

    // With reset inactive and enabled, Q accumulates D.
    check_accumulate_when_enabled: assert property (
        @(posedge CLK) disable iff (!AR) E |-> (Q == ($past(Q) + $past(D)))
    );

    // With reset inactive and disabled, Q holds its value.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (!AR) !E |-> (Q == $past(Q))
    );

    // The first cycle after reset release starts from zero.
    check_first_cycle_after_reset: assert property (
        @(posedge CLK) $rose(AR) |-> (Q == {N{1'b0}})
    );

endmodule
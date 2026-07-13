module dffsre_sva (
    input logic Q,
    input logic D,
    input logic C,
    input logic E,
    input logic R,
    input logic S
);

    // Q holds its value when enable is low.
    check_hold_when_disabled: assert property (
        @(posedge C) (!E) |=> (Q == $past(Q))
    );

    // Q is set high when enabled with set asserted and reset deasserted.
    check_set_when_enabled: assert property (
        @(posedge C) (E && S && !R) |=> (Q == 1'b1)
    );

    // Q is cleared when enabled with reset asserted and set deasserted.
    check_reset_when_enabled: assert property (
        @(posedge C) (E && !S && R) |=> (Q == 1'b0)
    );

    // Q captures D when enabled with neither set nor reset asserted.
    check_data_capture_when_enabled: assert property (
        @(posedge C) (E && !S && !R) |=> (Q == $past(D))
    );

    // Set has priority over reset when both are asserted with enable.
    check_set_priority_over_reset: assert property (
        @(posedge C) (E && S && R) |=> (Q == 1'b1)
    );

endmodule
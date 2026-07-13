module dff_en_sr_sva (
    input logic CLK,
    input logic D,
    input logic EN,
    input logic SET,
    input logic RESET,
    input logic Q,
    input logic Q_bar
);

    // Q_bar is always the inverse of Q.
    check_qbar_complement: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |-> (Q_bar == ~Q)
    );

    // When enabled, SET drives the set state and overrides RESET.
    check_set_path: assert property (
        @(posedge CLK) disable iff (1'b0)
        (EN && SET) |=> (Q == 1'b1 && Q_bar == 1'b0)
    );

    // When enabled and SET is low, RESET drives the reset state.
    check_reset_path: assert property (
        @(posedge CLK) disable iff (1'b0)
        (EN && !SET && RESET) |=> (Q == 1'b0 && Q_bar == 1'b1)
    );

    // When enabled with no set/reset, the flop captures D.
    check_data_capture_path: assert property (
        @(posedge CLK) disable iff (1'b0)
        (EN && !SET && !RESET) |=> (Q == $past(D) && Q_bar == (~$past(D)))
    );

    // When not enabled, both outputs hold their previous values.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!EN) |=> ($stable(Q) && $stable(Q_bar))
    );

endmodule
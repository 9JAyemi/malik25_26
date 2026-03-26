module Multiplexer_AC__parameterized33_sva (
    input logic clk,
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] D2,
    input logic [0:0] S
);

    // When ctrl is low, the output selects D0.
    check_select_d0_when_ctrl_low: assert property (
        @(posedge clk) (ctrl === 1'b0) |-> (S === D0)
    );

    // When ctrl is high, the unmatched selector drives zero.
    check_default_zero_when_ctrl_high: assert property (
        @(posedge clk) (ctrl === 1'b1) |-> (S === 1'b0)
    );

    // A rising ctrl drives the output to zero.
    check_ctrl_rise_forces_zero: assert property (
        @(posedge clk) $rose(ctrl) |-> (S === 1'b0)
    );

    // A falling ctrl makes the output select D0.
    check_ctrl_fall_selects_d0: assert property (
        @(posedge clk) $fell(ctrl) |-> (S === D0)
    );

    // D1 alone cannot affect the output when ctrl selects D0.
    check_d1_ignored_when_ctrl_low: assert property (
        @(posedge clk)
        (ctrl === 1'b0 && $stable(ctrl) && $stable(D0) && $changed(D1) && $stable(D2))
        |-> $stable(S)
    );

    // D2 alone cannot affect the output when ctrl selects D0.
    check_d2_ignored_when_ctrl_low: assert property (
        @(posedge clk)
        (ctrl === 1'b0 && $stable(ctrl) && $stable(D0) && $stable(D1) && $changed(D2))
        |-> $stable(S)
    );

endmodule
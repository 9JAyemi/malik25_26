module Multiplexer_AC__parameterized147__1_sva (
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);

    // S must always match the mux expression.
    check_mux_function: assert property (
        @($global_clock) (S == (ctrl ? D1 : D0))
    );

    // When ctrl is low, S must select D0.
    check_select_d0: assert property (
        @($global_clock) (!ctrl) |-> (S == D0)
    );

    // When ctrl is high, S must select D1.
    check_select_d1: assert property (
        @($global_clock) (ctrl) |-> (S == D1)
    );

    // A rising ctrl must make S select D1.
    check_ctrl_rise_selects_d1: assert property (
        @($global_clock) $rose(ctrl) |-> (S == D1)
    );

    // A falling ctrl must make S select D0.
    check_ctrl_fall_selects_d0: assert property (
        @($global_clock) $fell(ctrl) |-> (S == D0)
    );

endmodule
module Multiplexer_AC__parameterized128_sva (
    input logic         ctrl,
    input logic [127:0] D0,
    input logic [127:0] D1,
    input logic [127:0] S
);

    // Output always follows the mux equation.
    check_mux_equation: assert property (
        @($global_clock) S == (ctrl ? D1 : D0)
    );

    // Low control selects D0.
    check_select_d0_when_ctrl_low: assert property (
        @($global_clock) !ctrl |-> (S == D0)
    );

    // High control selects D1.
    check_select_d1_when_ctrl_high: assert property (
        @($global_clock) ctrl |-> (S == D1)
    );

    // A rising control value switches the output to D1.
    check_ctrl_rise_switches_to_d1: assert property (
        @($global_clock) $rose(ctrl) |-> (S == D1)
    );

    // A falling control value switches the output to D0.
    check_ctrl_fall_switches_to_d0: assert property (
        @($global_clock) $fell(ctrl) |-> (S == D0)
    );

    // Equal data inputs force the same output regardless of control.
    check_equal_inputs_same_output: assert property (
        @($global_clock) (D0 == D1) |-> (S == D0)
    );

endmodule
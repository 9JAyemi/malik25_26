module mux_2to1_sva #(
    parameter WIDTH = 1
) (
    input logic ctrl,
    input logic [WIDTH-1:0] D0,
    input logic [WIDTH-1:0] D1,
    input logic [WIDTH-1:0] S
);

    // No clock or reset exists in the RTL; sample on the formal global clock.

    // When ctrl is exactly 0, the output selects D0.
    check_select_d0_when_ctrl_low: assert property (
        @($global_clock) (ctrl === 1'b0) |-> (S === D0)
    );

    // When ctrl is not exactly 0, the output selects D1.
    check_select_d1_when_ctrl_not_low: assert property (
        @($global_clock) (ctrl !== 1'b0) |-> (S === D1)
    );

    // The output always matches one of the two inputs.
    check_output_matches_one_input: assert property (
        @($global_clock) ((S === D0) || (S === D1))
    );

    // If both inputs are equal, the output matches that common value.
    check_equal_inputs_passthrough: assert property (
        @($global_clock) (D0 === D1) |-> (S === D0)
    );

endmodule
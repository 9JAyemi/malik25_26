module counter_sva #(
    parameter WIDTH = 8,
    parameter DECREMENT_VALUE = 1
) (
    input logic clock,
    input logic reset,
    input logic enable,
    input logic [WIDTH-1:0] input_value,
    input logic [WIDTH-1:0] output_value
);

    localparam logic [WIDTH-1:0] ZERO = '0;
    localparam logic [WIDTH-1:0] DEC_VALUE_W = DECREMENT_VALUE;

    // Reset clears the counter output on the following clock.
    check_reset_clears_output: assert property (
        @(posedge clock) reset |=> (output_value == ZERO)
    );

    // Reset has priority over enable when both are asserted.
    check_reset_priority_over_enable: assert property (
        @(posedge clock) reset && enable |=> (output_value == ZERO)
    );

    // Enable loads input_value minus the decrement value.
    check_enable_loads_decremented_input: assert property (
        @(posedge clock) disable iff (reset)
        enable |=> (output_value == ($past(input_value) - DEC_VALUE_W))
    );

    // When enable is low, the counter output holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clock) disable iff (reset)
        !enable |=> (output_value == $past(output_value))
    );

endmodule
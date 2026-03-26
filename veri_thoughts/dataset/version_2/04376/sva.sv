module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic shift_left,
    input logic shift_right,
    input logic [3:0] result
);

    // Result must match the selected shift or passthrough behavior.
    check_result_function: assert property (
        @(posedge clk)
        result == (shift_left ? (A << B) : (shift_right ? (A >> B) : A))
    );

    // shift_left selects the left-shifted value.
    check_left_shift_result: assert property (
        @(posedge clk)
        shift_left |-> (result == (A << B))
    );

    // shift_right selects the right-shifted value when shift_left is low.
    check_right_shift_result: assert property (
        @(posedge clk)
        (!shift_left && shift_right) |-> (result == (A >> B))
    );

    // With no shift request, result passes A through unchanged.
    check_passthrough_result: assert property (
        @(posedge clk)
        (!shift_left && !shift_right) |-> (result == A)
    );

    // If both controls are high, shift_left has priority over shift_right.
    check_left_priority: assert property (
        @(posedge clk)
        (shift_left && shift_right) |-> (result == (A << B))
    );

endmodule
module calculator_sva(
    input logic signed [15:0] A,
    input logic signed [15:0] B,
    input logic [1:0] op,
    input logic signed [15:0] result
);

    // No RTL clock or reset; sample on the formal global clock.

    // Addition returns A plus B.
    check_addition_result: assert property (
        @($global_clock) (op == 2'b00) |-> (result == (A + B))
    );

    // Subtraction returns A minus B.
    check_subtraction_result: assert property (
        @($global_clock) (op == 2'b01) |-> (result == (A - B))
    );

    // Multiplication returns A times B.
    check_multiplication_result: assert property (
        @($global_clock) (op == 2'b10) |-> (result == (A * B))
    );

    // Division by zero returns 16'hFFFF.
    check_divide_by_zero_result: assert property (
        @($global_clock) ((op == 2'b11) && (B == 16'sd0)) |-> (result == 16'hFFFF)
    );

    // Division returns A divided by B when B is nonzero.
    check_division_result: assert property (
        @($global_clock) ((op == 2'b11) && (B != 16'sd0)) |-> (result == (A / B))
    );

endmodule
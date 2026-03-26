module output_generator_sva (
    input logic       clk,
    input logic [3:0] num1,
    input logic [3:0] num2,
    input logic [1:0] operation,
    input logic [3:0] result
);

    // Addition selects num1 + num2 truncated to 4 bits.
    check_addition_result: assert property (
        @(posedge clk)
        (operation == 2'b00) |-> (result == ((num1 + num2) & 4'hF))
    );

    // Subtraction selects num1 - num2 truncated to 4 bits.
    check_subtraction_result: assert property (
        @(posedge clk)
        (operation == 2'b01) |-> (result == ((num1 - num2) & 4'hF))
    );

    // Multiplication selects num1 * num2 truncated to 4 bits.
    check_multiplication_result: assert property (
        @(posedge clk)
        (operation == 2'b10) |-> (result == ((num1 * num2) & 4'hF))
    );

    // Division selects num1 / num2 when the divisor is nonzero.
    check_division_result: assert property (
        @(posedge clk)
        (operation == 2'b11 && num2 != 4'h0) |-> (result == (num1 / num2))
    );

    // Invalid or unknown operation values drive zero by the default case.
    check_default_result: assert property (
        @(posedge clk)
        ((operation !== 2'b00) && (operation !== 2'b01) && (operation !== 2'b10) && (operation !== 2'b11))
        |-> (result == 4'h0)
    );

    // Stable sampled inputs imply a stable sampled result.
    check_stable_inputs_stable_result: assert property (
        @(posedge clk)
        (!$initstate && $stable({num1, num2, operation})) |-> $stable(result)
    );

endmodule
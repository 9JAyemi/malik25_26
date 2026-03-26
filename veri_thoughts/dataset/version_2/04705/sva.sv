module calculator_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [1:0] ctrl,
    input logic [3:0] result
);

    // Addition mode computes the 4-bit sum.
    check_addition_mode: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (result == ((a + b) & 4'hF))
    );

    // Subtraction mode computes the 4-bit difference.
    check_subtraction_mode: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (result == ((a - b) & 4'hF))
    );

    // Multiplication mode computes the low 4 bits of the product.
    check_multiplication_mode: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (result == ((a * b) & 4'hF))
    );

    // Division mode computes the quotient when the divisor is nonzero.
    check_division_mode_nonzero: assert property (
        @(posedge clk) ((ctrl == 2'b11) && (b != 4'h0)) |-> (result == ((a / b) & 4'hF))
    );

    // Stable sampled inputs imply a stable sampled result.
    check_result_stable_when_inputs_stable: assert property (
        @(posedge clk) (!$initstate && $stable(a) && $stable(b) && $stable(ctrl) && !((ctrl == 2'b11) && (b == 4'h0))) |-> $stable(result)
    );

endmodule
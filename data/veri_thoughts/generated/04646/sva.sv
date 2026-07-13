module simple_calculator_sva (
    input logic clk,
    input logic signed [7:0] a,
    input logic signed [7:0] b,
    input logic signed [7:0] add_out,
    input logic signed [7:0] sub_out,
    input logic signed [7:0] mul_out,
    input logic signed [7:0] div_out,
    input logic [1:0] op
);

    typedef logic signed [7:0] s8_t;

    // Addition mode computes the sum and clears the other outputs.
    check_addition_mode: assert property (
        @(posedge clk)
        (op == 2'b00) |-> ((add_out == s8_t'(a + b)) &&
                           (sub_out == 8'sd0) &&
                           (mul_out == 8'sd0) &&
                           (div_out == 8'sd0))
    );

    // Subtraction mode computes the difference and clears the other outputs.
    check_subtraction_mode: assert property (
        @(posedge clk)
        (op == 2'b01) |-> ((add_out == 8'sd0) &&
                           (sub_out == s8_t'(a - b)) &&
                           (mul_out == 8'sd0) &&
                           (div_out == 8'sd0))
    );

    // Multiplication mode computes the product and clears the other outputs.
    check_multiplication_mode: assert property (
        @(posedge clk)
        (op == 2'b10) |-> ((add_out == 8'sd0) &&
                           (sub_out == 8'sd0) &&
                           (mul_out == s8_t'(a * b)) &&
                           (div_out == 8'sd0))
    );

    // Division mode computes the quotient for nonzero divisors and clears the other outputs.
    check_division_mode: assert property (
        @(posedge clk)
        ((op == 2'b11) && (b != 8'sd0)) |-> ((add_out == 8'sd0) &&
                                             (sub_out == 8'sd0) &&
                                             (mul_out == 8'sd0) &&
                                             (div_out == s8_t'(a / b)))
    );

    // add_out is cleared whenever addition is not selected.
    check_add_out_cleared_when_not_add: assert property (
        @(posedge clk)
        (op != 2'b00) |-> (add_out == 8'sd0)
    );

    // sub_out is cleared whenever subtraction is not selected.
    check_sub_out_cleared_when_not_sub: assert property (
        @(posedge clk)
        (op != 2'b01) |-> (sub_out == 8'sd0)
    );

    // mul_out is cleared whenever multiplication is not selected.
    check_mul_out_cleared_when_not_mul: assert property (
        @(posedge clk)
        (op != 2'b10) |-> (mul_out == 8'sd0)
    );

    // div_out is cleared whenever division is not selected.
    check_div_out_cleared_when_not_div: assert property (
        @(posedge clk)
        (op != 2'b11) |-> (div_out == 8'sd0)
    );

endmodule
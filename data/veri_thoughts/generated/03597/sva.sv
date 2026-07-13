module calculator_sva (
    input logic clk,
    input logic signed [15:0] a,
    input logic signed [15:0] b,
    input logic [1:0] op,
    input logic signed [15:0] add_out,
    input logic signed [15:0] sub_out,
    input logic signed [15:0] mul_out,
    input logic signed [15:0] div_out
);

    function automatic logic signed [15:0] calc_add (
        input logic signed [15:0] x,
        input logic signed [15:0] y
    );
        calc_add = x + y;
    endfunction

    function automatic logic signed [15:0] calc_sub (
        input logic signed [15:0] x,
        input logic signed [15:0] y
    );
        calc_sub = x - y;
    endfunction

    function automatic logic signed [15:0] calc_mul (
        input logic signed [15:0] x,
        input logic signed [15:0] y
    );
        calc_mul = x * y;
    endfunction

    function automatic logic signed [15:0] calc_div (
        input logic signed [15:0] x,
        input logic signed [15:0] y
    );
        if (y != 16'sh0000)
            calc_div = x / y;
        else
            calc_div = 16'shFFFF;
    endfunction

    // Addition mode drives the sum and clears the other outputs.
    check_addition_mode_outputs: assert property (
        @(posedge clk)
        (op == 2'b00) |-> ((add_out == calc_add(a, b)) &&
                           (sub_out == 16'sh0000) &&
                           (mul_out == 16'sh0000) &&
                           (div_out == 16'sh0000))
    );

    // Subtraction mode drives the difference and clears the other outputs.
    check_subtraction_mode_outputs: assert property (
        @(posedge clk)
        (op == 2'b01) |-> ((add_out == 16'sh0000) &&
                           (sub_out == calc_sub(a, b)) &&
                           (mul_out == 16'sh0000) &&
                           (div_out == 16'sh0000))
    );

    // Multiplication mode drives the product and clears the other outputs.
    check_multiplication_mode_outputs: assert property (
        @(posedge clk)
        (op == 2'b10) |-> ((add_out == 16'sh0000) &&
                           (sub_out == 16'sh0000) &&
                           (mul_out == calc_mul(a, b)) &&
                           (div_out == 16'sh0000))
    );

    // Division mode with a nonzero divisor drives the quotient and clears the other outputs.
    check_division_mode_nonzero_divisor: assert property (
        @(posedge clk)
        ((op == 2'b11) && (b != 16'sh0000)) |-> ((add_out == 16'sh0000) &&
                                                 (sub_out == 16'sh0000) &&
                                                 (mul_out == 16'sh0000) &&
                                                 (div_out == calc_div(a, b)))
    );

    // Division by zero returns 16'hFFFF and clears the other outputs.
    check_division_mode_zero_divisor: assert property (
        @(posedge clk)
        ((op == 2'b11) && (b == 16'sh0000)) |-> ((add_out == 16'sh0000) &&
                                                 (sub_out == 16'sh0000) &&
                                                 (mul_out == 16'sh0000) &&
                                                 (div_out == 16'shFFFF))
    );

endmodule
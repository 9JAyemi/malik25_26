module calculator_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);

    // Sample the combinational DUT on the global formal clock.
    
    // Addition returns the 8-bit sum of a and b.
    check_addition_result: assert property (
        @($global_clock)
        (op == 2'b00) |-> (result == (a + b))
    );

    // Subtraction returns the 8-bit difference of a and b.
    check_subtraction_result: assert property (
        @($global_clock)
        (op == 2'b01) |-> (result == (a - b))
    );

    // Multiplication saturates to 8'hFF when the product exceeds 8 bits.
    check_multiply_saturates: assert property (
        @($global_clock)
        (op == 2'b10 && (({8'h00, a} * {8'h00, b}) > 16'h00FF)) |-> (result == 8'hFF)
    );

    // Multiplication returns the exact product when it fits in 8 bits.
    check_multiply_exact: assert property (
        @($global_clock)
        (op == 2'b10 && (({8'h00, a} * {8'h00, b}) <= 16'h00FF)) |-> (result == ({8'h00, a} * {8'h00, b}))
    );

    // Division by zero returns 8'hFF.
    check_divide_by_zero: assert property (
        @($global_clock)
        (op == 2'b11 && (b == 8'h00)) |-> (result == 8'hFF)
    );

    // Division by a nonzero divisor returns the quotient.
    check_divide_result: assert property (
        @($global_clock)
        (op == 2'b11 && (b != 8'h00)) |-> (result == (a / b))
    );

    // Stable inputs keep the combinational result stable.
    check_stable_inputs_stable_result: assert property (
        @($global_clock)
        ($stable(a) && $stable(b) && $stable(op)) |-> $stable(result)
    );

endmodule
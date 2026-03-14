module simple_calculator_sva (
    input logic [15:0] operand_a,
    input logic [15:0] operand_b,
    input logic [1:0]  operation,
    input logic [15:0] result
);
    // No clock/reset in RTL; pure combinational. Use $global_clock for assertions.

    // Addition result matches lower 16 bits of sum when operation == 00.
    check_addition_result: assert property (
        @(posedge $global_clock) (operation == 2'b00) |-> (result == (operand_a + operand_b)[15:0])
    );

    // Subtraction result matches lower 16 bits of difference when operation == 01.
    check_subtraction_result: assert property (
        @(posedge $global_clock) (operation == 2'b01) |-> (result == (operand_a - operand_b)[15:0])
    );

    // Multiplication result matches lower 16 bits of product when operation == 10.
    check_multiplication_result: assert property (
        @(posedge $global_clock) (operation == 2'b10) |-> (result == (operand_a * operand_b)[15:0])
    );

    // Division result matches quotient when operation == 11 and divisor != 0.
    check_division_result_nonzero: assert property (
        @(posedge $global_clock) (operation == 2'b11 && (operand_b != 16'h0000)) |-> (result == (operand_a / operand_b)[15:0])
    );

    // Addition by zero returns operand_a.
    check_add_zero_identity: assert property (
        @(posedge $global_clock) (operation == 2'b00 && operand_b == 16'h0000) |-> (result == operand_a)
    );

    // Subtraction by zero returns operand_a.
    check_sub_zero_identity: assert property (
        @(posedge $global_clock) (operation == 2'b01 && operand_b == 16'h0000) |-> (result == operand_a)
    );

    // Subtraction of equal operands yields zero.
    check_sub_self_zero: assert property (
        @(posedge $global_clock) (operation == 2'b01 && operand_a == operand_b) |-> (result == 16'h0000)
    );

    // Multiplication by zero yields zero.
    check_mul_zero_annihilator: assert property (
        @(posedge $global_clock) (operation == 2'b10 && (operand_a == 16'h0000 || operand_b == 16'h0000)) |-> (result == 16'h0000)
    );

    // Multiplication by one returns operand_a.
    check_mul_one_identity: assert property (
        @(posedge $global_clock) (operation == 2'b10 && operand_b == 16'h0001) |-> (result == operand_a)
    );

    // Division by one returns operand_a.
    check_div_one_identity: assert property (
        @(posedge $global_clock) (operation == 2'b11 && operand_b == 16'h0001) |-> (result == operand_a)
    );
endmodule
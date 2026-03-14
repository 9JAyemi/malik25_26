module calculator_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] operation,
    input logic [15:0] result
);
    ///// Functional correctness per operation (1-cycle latency) /////
    // On add, result equals previous cycle's 16-bit zero-extended A+B.
    check_addition_result: assert property (
        @(posedge clk) ($past(operation) == 2'b00) |-> (result == $past({8'b0, A} + {8'b0, B}))
    );
    // On subtract, result equals previous cycle's 16-bit zero-extended A-B.
    check_subtraction_result: assert property (
        @(posedge clk) ($past(operation) == 2'b01) |-> (result == $past({8'b0, A} - {8'b0, B}))
    );
    // On multiply, result equals previous cycle's lower 16 bits of 24x24 product.
    check_multiplication_result: assert property (
        @(posedge clk) ($past(operation) == 2'b10) |-> (result == $past(({16'b0, A} * {16'b0, B})[15:0]))
    );
    // On divide with nonzero divisor, result equals previous cycle's lower 16 bits of 24/24 quotient.
    check_division_result_nonzero: assert property (
        @(posedge clk) ($past(operation) == 2'b11 && $past(B) != 8'd0) |-> (result == $past(({16'b0, A} / {16'b0, B})[15:0]))
    );

    ///// Identities and corner cases derived from the RTL arithmetic /////
    // Add: if A was zero, result equals previous zero-extended B.
    add_identity_A_zero: assert property (
        @(posedge clk) ($past(operation) == 2'b00 && $past(A) == 8'd0) |-> (result == $past({8'b0, B}))
    );
    // Add: if B was zero, result equals previous zero-extended A.
    add_identity_B_zero: assert property (
        @(posedge clk) ($past(operation) == 2'b00 && $past(B) == 8'd0) |-> (result == $past({8'b0, A}))
    );
    // Sub: if B was zero, result equals previous zero-extended A.
    sub_identity_B_zero: assert property (
        @(posedge clk) ($past(operation) == 2'b01 && $past(B) == 8'd0) |-> (result == $past({8'b0, A}))
    );
    // Sub: if A and B were equal, result is zero.
    sub_equal_operands_zero: assert property (
        @(posedge clk) ($past(operation) == 2'b01 && ($past(A) == $past(B))) |-> (result == 16'd0)
    );
    // Mul: if either operand was zero, result is zero.
    mul_zero_produces_zero: assert property (
        @(posedge clk) ($past(operation) == 2'b10 && ($past(A) == 8'd0 || $past(B) == 8'd0)) |-> (result == 16'd0)
    );
    // Mul: if A was 1, result equals previous zero-extended B.
    mul_by_one_A_identity: assert property (
        @(posedge clk) ($past(operation) == 2'b10 && $past(A) == 8'd1) |-> (result == $past({8'b0, B}))
    );
    // Mul: if B was 1, result equals previous zero-extended A.
    mul_by_one_B_identity: assert property (
        @(posedge clk) ($past(operation) == 2'b10 && $past(B) == 8'd1) |-> (result == $past({8'b0, A}))
    );
    // Div: if divisor was 1, result equals previous zero-extended A.
    div_by_one_identity: assert property (
        @(posedge clk) ($past(operation) == 2'b11 && $past(B) == 8'd1) |-> (result == $past({8'b0, A}))
    );
endmodule
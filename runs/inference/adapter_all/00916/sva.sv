module calculator_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);
    // Addition: result equals a + b (8-bit wrap).
    check_add_result: assert property (
        @(posedge a[0]) (op == 2'b00) |-> (result == (a + b))
    );

    // Subtraction: result equals a - b (8-bit wrap).
    check_sub_result: assert property (
        @(posedge a[0]) (op == 2'b01) |-> (result == (a - b))
    );

    // Multiplication: result equals a * b (low 8 bits, wrap).
    check_mul_result: assert property (
        @(posedge a[0]) (op == 2'b10) |-> (result == (a * b)[7:0])
    );

    // Division: result equals a / b when b != 0.
    check_div_result: assert property (
        @(posedge a[0]) (op == 2'b11 && b != 8'd0) |-> (result == (a / b))
    );

    // For division by 1, result equals a.
    check_div_by_one_identity: assert property (
        @(posedge a[0]) (op == 2'b11 && b == 8'd1) |-> (result == a)
    );

    // For multiplication by 0, result is 0.
    check_mul_zero_identity: assert property (
        @(posedge a[0]) (op == 2'b10 && (a == 8'd0 || b == 8'd0)) |-> (result == 8'd0)
    );

    // For addition with b==0, result equals a.
    check_add_zero_identity: assert property (
        @(posedge a[0]) (op == 2'b00 && b == 8'd0) |-> (result == a)
    );

    // For subtraction with b==0, result equals a.
    check_sub_zero_identity: assert property (
        @(posedge a[0]) (op == 2'b01 && b == 8'd0) |-> (result == a)
    );

    // For subtraction with a==b, result is 0.
    check_sub_equal_operands_zero: assert property (
        @(posedge a[0]) (op == 2'b01 && a == b) |-> (result == 8'd0)
    );

    // For division with a==b, result is 1 (when b!=0).
    check_div_equal_operands_one: assert property (
        @(posedge a[0]) (op == 2'b11 && a == b && b != 8'd0) |-> (result == 8'd1)
    );
endmodule
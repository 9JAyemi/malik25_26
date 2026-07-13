module calculator_sva (
    // DUT ports
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result,
    // Checker clock (DUT is combinational; assertions are sampled on this clock)
    input logic clk
);
    // Analysis: No clock/reset in DUT; purely combinational; result selects a+b, a-b, a*b, a/b by op.

    // For op==00, result equals a+b truncated to 8 bits.
    check_add_operation: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == (a + b)[7:0])
    );

    // For op==01, result equals a-b truncated to 8 bits.
    check_sub_operation: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == (a - b)[7:0])
    );

    // For op==10, result equals low 8 bits of a*b.
    check_mul_operation: assert property (
        @(posedge clk) (op == 2'b10) |-> (result == (a * b)[7:0])
    );

    // For op==11 with nonzero divisor, result equals a/b.
    check_div_operation_nonzero: assert property (
        @(posedge clk) (op == 2'b11 && b != 8'd0) |-> (result == (a / b)[7:0])
    );

    // If inputs a,b,op do not change, result must not change.
    check_pure_function_stability: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && $stable(op)) |-> $stable(result)
    );

    // For add: adding zero from a side yields the other operand.
    check_add_zero_a: assert property (
        @(posedge clk) (op == 2'b00 && a == 8'd0) |-> (result == b)
    );

    // For add: adding zero from b side yields the other operand.
    check_add_zero_b: assert property (
        @(posedge clk) (op == 2'b00 && b == 8'd0) |-> (result == a)
    );

    // For sub: subtracting zero yields the minuend.
    check_sub_zero: assert property (
        @(posedge clk) (op == 2'b01 && b == 8'd0) |-> (result == a)
    );

    // For sub: subtracting equal operands yields zero.
    check_sub_equal_zero: assert property (
        @(posedge clk) (op == 2'b01 && a == b) |-> (result == 8'd0)
    );

    // For mul: multiplying by zero on a side yields zero.
    check_mul_zero_a: assert property (
        @(posedge clk) (op == 2'b10 && a == 8'd0) |-> (result == 8'd0)
    );

    // For mul: multiplying by zero on b side yields zero.
    check_mul_zero_b: assert property (
        @(posedge clk) (op == 2'b10 && b == 8'd0) |-> (result == 8'd0)
    );

    // For mul: multiplying by one on a side yields the other operand.
    check_mul_one_a: assert property (
        @(posedge clk) (op == 2'b10 && a == 8'd1) |-> (result == b)
    );

    // For mul: multiplying by one on b side yields the other operand.
    check_mul_one_b: assert property (
        @(posedge clk) (op == 2'b10 && b == 8'd1) |-> (result == a)
    );

    // For div: dividing by one yields the dividend.
    check_div_one: assert property (
        @(posedge clk) (op == 2'b11 && b == 8'd1) |-> (result == a)
    );
endmodule
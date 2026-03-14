module ArithmeticUnit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] C,
    input logic [3:0] R
);
    // For C==000, R equals 4-bit sum of A and B (wraps on overflow).
    check_addition_result: assert property (
        @(posedge clk) (C == 3'b000) |-> (R === (A + B))
    );

    // For C==001, R equals 4-bit difference A - B (wraps on underflow).
    check_subtraction_result: assert property (
        @(posedge clk) (C == 3'b001) |-> (R === (A - B))
    );

    // For all other C values, R is driven to zero.
    check_default_zero: assert property (
        @(posedge clk) ((C != 3'b000) && (C != 3'b001)) |-> (R === 4'b0000)
    );

    // Addition identity: adding zero on B passes A through.
    check_add_zero_b: assert property (
        @(posedge clk) ((C == 3'b000) && (B == 4'b0000)) |-> (R === A)
    );

    // Addition identity: adding zero on A passes B through.
    check_add_zero_a: assert property (
        @(posedge clk) ((C == 3'b000) && (A == 4'b0000)) |-> (R === B)
    );

    // Subtraction identity: subtracting zero passes A through.
    check_sub_zero_b: assert property (
        @(posedge clk) ((C == 3'b001) && (B == 4'b0000)) |-> (R === A)
    );

    // Subtraction of equal operands yields zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) ((C == 3'b001) && (A == B)) |-> (R === 4'b0000)
    );

    // When adding equal operands, result equals A<<1 (4-bit wrap).
    check_add_double_when_equal: assert property (
        @(posedge clk) ((C == 3'b000) && (A == B)) |-> (R === (A << 1))
    );

    // Example wrap on addition: 0xF + 1 => 0x0.
    check_add_wrap_example: assert property (
        @(posedge clk) ((C == 3'b000) && (A == 4'hF) && (B == 4'h1)) |-> (R === 4'h0)
    );

    // Example borrow on subtraction: 0x0 - 1 => 0xF.
    check_sub_borrow_example: assert property (
        @(posedge clk) ((C == 3'b001) && (A == 4'h0) && (B == 4'h1)) |-> (R === 4'hF)
    );
endmodule
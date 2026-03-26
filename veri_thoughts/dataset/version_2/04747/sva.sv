module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [1:0] shift_type,
    input logic select,
    input logic [3:0] B
);

    // In multiply mode, B is the low 4 bits of A*3.
    check_mul_mode_output: assert property (
        @(posedge clk)
        (select == 1'b0) |-> (B == (A + (A << 1)))
    );

    // In shift mode with 00, B is A logically shifted left by 1.
    check_shift_mode_logical_left: assert property (
        @(posedge clk)
        (select == 1'b1 && shift_type == 2'b00) |-> (B == (A << 1))
    );

    // In shift mode with 01, B is A logically shifted right by 1.
    check_shift_mode_logical_right: assert property (
        @(posedge clk)
        (select == 1'b1 && shift_type == 2'b01) |-> (B == (A >> 1))
    );

    // In shift mode with 10, B matches the RTL concatenation.
    check_shift_mode_case_10: assert property (
        @(posedge clk)
        (select == 1'b1 && shift_type == 2'b10) |-> (B == {A[2], A[3], A[3], A[3]})
    );

    // In shift mode with 11, B matches the RTL concatenation.
    check_shift_mode_case_11: assert property (
        @(posedge clk)
        (select == 1'b1 && shift_type == 2'b11) |-> (B == {A[0], A[0], A[0], A[1]})
    );

endmodule
module add_subtract_sva (
    input logic clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic MODE,
    input logic CIN,
    input logic [15:0] Q
);

    // In add mode, Q equals A + B + CIN.
    check_add_mode_result: assert property (
        @(posedge clk) (MODE == 1'b0) |-> (Q == (A + B + CIN))
    );

    // In subtract mode, Q equals A - B - CIN.
    check_subtract_mode_result: assert property (
        @(posedge clk) (MODE == 1'b1) |-> (Q == (A - B - CIN))
    );

    // With B and CIN cleared, the output passes A through.
    check_passthrough_when_b_and_cin_zero: assert property (
        @(posedge clk) (B == 16'h0000 && CIN == 1'b0) |-> (Q == A)
    );

    // With all arithmetic inputs zero, the output is zero.
    check_zero_result_for_zero_inputs: assert property (
        @(posedge clk) (A == 16'h0000 && B == 16'h0000 && CIN == 1'b0) |-> (Q == 16'h0000)
    );

    // Subtracting equal operands with no borrow-in yields zero.
    check_subtract_equal_operands_zero: assert property (
        @(posedge clk) (MODE == 1'b1 && A == B && CIN == 1'b0) |-> (Q == 16'h0000)
    );

endmodule
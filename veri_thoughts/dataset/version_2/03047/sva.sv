module barrel_shifter_sva (
    input logic clk,
    input logic [15:0] A,
    input logic [3:0] B,
    input logic [15:0] shift_left,
    input logic [15:0] shift_right
);

    // shift_left must implement A logically shifted left by B.
    check_shift_left_function: assert property (
        @(posedge clk) shift_left == (A << B)
    );

    // shift_right must implement A logically shifted right by B.
    check_shift_right_function: assert property (
        @(posedge clk) shift_right == (A >> B)
    );

    // A zero shift amount must pass A through on shift_left.
    check_shift_left_zero_amount: assert property (
        @(posedge clk) (B == 4'd0) |-> (shift_left == A)
    );

    // A zero shift amount must pass A through on shift_right.
    check_shift_right_zero_amount: assert property (
        @(posedge clk) (B == 4'd0) |-> (shift_right == A)
    );

    // Left shifts must zero-fill the vacated LSBs.
    check_shift_left_zero_fill: assert property (
        @(posedge clk) (B != 4'd0) |-> ((shift_left & ((16'h0001 << B) - 16'h0001)) == 16'h0000)
    );

    // Right shifts must zero-fill the vacated MSBs.
    check_shift_right_zero_fill: assert property (
        @(posedge clk) (B != 4'd0) |-> ((shift_right & (16'hFFFF << (5'd16 - {1'b0, B}))) == 16'h0000)
    );

    // A shift by 15 leaves only A[0] in the shift_left MSB.
    check_shift_left_max_amount: assert property (
        @(posedge clk) (B == 4'd15) |-> (shift_left == {A[0], 15'b0})
    );

    // A shift by 15 leaves only A[15] in the shift_right LSB.
    check_shift_right_max_amount: assert property (
        @(posedge clk) (B == 4'd15) |-> (shift_right == {15'b0, A[15]})
    );

endmodule
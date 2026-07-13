module shift_left_assertions (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] out
);

    // Output is zero when the shift amount exceeds the 4-bit width.
    check_zero_when_shift_too_large: assert property (
        @(posedge clk) (B > 4'd3) |-> (out == 4'b0000)
    );

    // Output equals A shifted left by B for valid shift amounts.
    check_shift_for_valid_range: assert property (
        @(posedge clk) (B <= 4'd3) |-> (out == (A << B))
    );

    // A zero shift amount passes A through unchanged.
    check_no_shift_when_B_zero: assert property (
        @(posedge clk) (B == 4'd0) |-> (out == A)
    );

    // A shift amount of one inserts one zero at the LSB.
    check_shift_by_one: assert property (
        @(posedge clk) (B == 4'd1) |-> (out == {A[2:0], 1'b0})
    );

    // A shift amount of two inserts two zeros at the LSBs.
    check_shift_by_two: assert property (
        @(posedge clk) (B == 4'd2) |-> (out == {A[1:0], 2'b00})
    );

    // A shift amount of three leaves only A[0] in the MSB position.
    check_shift_by_three: assert property (
        @(posedge clk) (B == 4'd3) |-> (out == {A[0], 3'b000})
    );

endmodule
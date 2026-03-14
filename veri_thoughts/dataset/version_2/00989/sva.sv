module barrel_shifter_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [1:0] B,
    input logic [3:0] Y
);
    // Y equals A when no shift selected (B==00).
    check_no_shift_mapping: assert property (
        @(posedge clk) (B == 2'b00) |-> (Y == A)
    );
    // Y equals A shifted left by 1 with zero-fill when B==01.
    check_shift_left1_mapping: assert property (
        @(posedge clk) (B == 2'b01) |-> (Y == {A[2:0], 1'b0})
    );
    // Y equals A shifted right by 1 with zero-fill when B==10.
    check_shift_right1_mapping: assert property (
        @(posedge clk) (B == 2'b10) |-> (Y == {1'b0, A[3:1]})
    );
    // Y equals A shifted right by 2 with zero-fill when B==11.
    check_shift_right2_mapping: assert property (
        @(posedge clk) (B == 2'b11) |-> (Y == {2'b00, A[3:2]})
    );
    // For left shift by 1, LSB is zero-filled.
    check_shift_left1_zero_lsb: assert property (
        @(posedge clk) (B == 2'b01) |-> (Y[0] == 1'b0)
    );
    // For right shift by 1, MSB is zero-filled.
    check_shift_right1_zero_msb: assert property (
        @(posedge clk) (B == 2'b10) |-> (Y[3] == 1'b0)
    );
    // For right shift by 2, two MSBs are zero-filled.
    check_shift_right2_zero_msbs: assert property (
        @(posedge clk) (B == 2'b11) |-> (Y[3:2] == 2'b00)
    );
    // For left shift by 1, upper bits map from A[2:0].
    check_shift_left1_upper_map: assert property (
        @(posedge clk) (B == 2'b01) |-> (Y[3:1] == A[2:0])
    );
    // For right shift by 1, lower bits map from A[3:1].
    check_shift_right1_lower_map: assert property (
        @(posedge clk) (B == 2'b10) |-> (Y[2:0] == A[3:1])
    );
    // For right shift by 2, lower two bits map from A[3:2].
    check_shift_right2_lower_map: assert property (
        @(posedge clk) (B == 2'b11) |-> (Y[1:0] == A[3:2])
    );
endmodule
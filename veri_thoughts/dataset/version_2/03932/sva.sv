module barrel_shifter_sva (
    input logic clk,
    input logic [15:0] A,
    input logic [3:0] shift,
    input logic [15:0] Y
);

    // shift=0 passes A through.
    check_shift_0_identity: assert property (
        @(posedge clk) (shift == 4'b0000) |-> (Y == A)
    );

    // shift=1 rotates A left by 1 bit.
    check_shift_1_rotate_left_1: assert property (
        @(posedge clk) (shift == 4'b0001) |-> (Y == {A[14:0], A[15]})
    );

    // shift=2 rotates A left by 2 bits.
    check_shift_2_rotate_left_2: assert property (
        @(posedge clk) (shift == 4'b0010) |-> (Y == {A[13:0], A[15:14]})
    );

    // shift=3 rotates A left by 3 bits.
    check_shift_3_rotate_left_3: assert property (
        @(posedge clk) (shift == 4'b0011) |-> (Y == {A[12:0], A[15:13]})
    );

    // shift=4 rotates A left by 4 bits.
    check_shift_4_rotate_left_4: assert property (
        @(posedge clk) (shift == 4'b0100) |-> (Y == {A[11:0], A[15:12]})
    );

    // shift=5 rotates A left by 5 bits.
    check_shift_5_rotate_left_5: assert property (
        @(posedge clk) (shift == 4'b0101) |-> (Y == {A[10:0], A[15:11]})
    );

    // shift=6 rotates A left by 6 bits.
    check_shift_6_rotate_left_6: assert property (
        @(posedge clk) (shift == 4'b0110) |-> (Y == {A[9:0], A[15:10]})
    );

    // shift=7 rotates A left by 7 bits.
    check_shift_7_rotate_left_7: assert property (
        @(posedge clk) (shift == 4'b0111) |-> (Y == {A[8:0], A[15:9]})
    );

    // shift=8 rotates A left by 8 bits.
    check_shift_8_rotate_left_8: assert property (
        @(posedge clk) (shift == 4'b1000) |-> (Y == {A[7:0], A[15:8]})
    );

    // shift=9 rotates A left by 9 bits.
    check_shift_9_rotate_left_9: assert property (
        @(posedge clk) (shift == 4'b1001) |-> (Y == {A[6:0], A[15:7]})
    );

    // shift=10 rotates A left by 10 bits.
    check_shift_10_rotate_left_10: assert property (
        @(posedge clk) (shift == 4'b1010) |-> (Y == {A[5:0], A[15:6]})
    );

    // shift=11 rotates A left by 11 bits.
    check_shift_11_rotate_left_11: assert property (
        @(posedge clk) (shift == 4'b1011) |-> (Y == {A[4:0], A[15:5]})
    );

    // shift=12 rotates A left by 12 bits.
    check_shift_12_rotate_left_12: assert property (
        @(posedge clk) (shift == 4'b1100) |-> (Y == {A[3:0], A[15:4]})
    );

    // shift=13 rotates A left by 13 bits.
    check_shift_13_rotate_left_13: assert property (
        @(posedge clk) (shift == 4'b1101) |-> (Y == {A[2:0], A[15:3]})
    );

    // shift=14 rotates A left by 14 bits.
    check_shift_14_rotate_left_14: assert property (
        @(posedge clk) (shift == 4'b1110) |-> (Y == {A[1:0], A[15:2]})
    );

    // shift=15 rotates A left by 15 bits.
    check_shift_15_rotate_left_15: assert property (
        @(posedge clk) (shift == 4'b1111) |-> (Y == {A[0], A[15:1]})
    );

endmodule
module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [1:0] SHIFT,
    input logic [3:0] Y
);

    // SHIFT=00 passes the input through unchanged.
    check_no_shift: assert property (
        @(posedge clk) (SHIFT == 2'b00) |-> (Y == A)
    );

    // SHIFT=01 shifts left by 1 and inserts 0 in bit 0.
    check_left_shift_by_1: assert property (
        @(posedge clk) (SHIFT == 2'b01) |-> (Y == {A[2:0], 1'b0})
    );

    // SHIFT=10 shifts right by 1 and inserts 0 in bit 3.
    check_right_shift_by_1: assert property (
        @(posedge clk) (SHIFT == 2'b10) |-> (Y == {1'b0, A[3:1]})
    );

    // SHIFT=11 maps the output to {A[1:0], A[3:2]}.
    check_shift_11_mapping: assert property (
        @(posedge clk) (SHIFT == 2'b11) |-> (Y == {A[1:0], A[3:2]})
    );

endmodule
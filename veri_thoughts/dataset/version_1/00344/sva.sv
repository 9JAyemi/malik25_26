module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] S,
    input logic [3:0] Y
);

    // Y must always match the selected rotation of A.
    check_output_matches_select: assert property (
        @(posedge clk)
        Y == ((S == 2'b00) ? A :
              (S == 2'b01) ? {A[2:0], A[3]} :
              (S == 2'b10) ? {A[0], A[3:1]} :
                             {A[1:0], A[3:2]})
    );

    // S=00 passes A through unchanged.
    check_sel_00_passthrough: assert property (
        @(posedge clk)
        (S == 2'b00) |-> (Y == A)
    );

    // S=01 rotates A left by one bit.
    check_sel_01_rotate_left_1: assert property (
        @(posedge clk)
        (S == 2'b01) |-> (Y == {A[2:0], A[3]})
    );

    // S=10 rotates A right by one bit.
    check_sel_10_rotate_right_1: assert property (
        @(posedge clk)
        (S == 2'b10) |-> (Y == {A[0], A[3:1]})
    );

    // S=11 rotates A by two bits.
    check_sel_11_rotate_2: assert property (
        @(posedge clk)
        (S == 2'b11) |-> (Y == {A[1:0], A[3:2]})
    );

endmodule
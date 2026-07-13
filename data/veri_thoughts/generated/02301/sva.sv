module barrel_shifter_sva (
    input logic CLK,          // External verification clock for sampling
    input logic [3:0] D,      // DUT input
    input logic [1:0] S,      // DUT input
    input logic [3:0] Q       // DUT output
);
    // No reset in RTL; purely combinational behavior sampled on CLK.

    // When S==00, Q passes D unchanged.
    check_no_shift: assert property (
        @(posedge CLK) (S == 2'b00) |-> (Q == D)
    );

    // When S==01, Q is left shift by 1 with zero fill.
    check_left_shift: assert property (
        @(posedge CLK) (S == 2'b01) |-> (Q == {D[2:0], 1'b0})
    );

    // For left shift, LSB is zero (zero-fill).
    check_left_shift_lsb_zero: assert property (
        @(posedge CLK) (S == 2'b01) |-> (Q[0] == 1'b0)
    );

    // When S==10, Q is right shift by 1 with zero fill.
    check_right_shift: assert property (
        @(posedge CLK) (S == 2'b10) |-> (Q == {1'b0, D[3:1]})
    );

    // For right shift, MSB is zero (zero-fill).
    check_right_shift_msb_zero: assert property (
        @(posedge CLK) (S == 2'b10) |-> (Q[3] == 1'b0)
    );

    // When S==11, Q is a circular rotate-left by 2 bits.
    check_circular_shift: assert property (
        @(posedge CLK) (S == 2'b11) |-> (Q == {D[1:0], D[3:2]})
    );
endmodule
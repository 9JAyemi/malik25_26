module barrel_shifter_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [3:0] shift_amt,
    input logic shift_left,
    input logic [15:0] out
);

// Left shift mode produces in shifted left by shift_amt.
    check_left_shift_result: assert property (
        @(posedge clk) shift_left |-> (out == (in << shift_amt))
    );

// Right shift mode produces in shifted right by shift_amt.
    check_right_shift_result: assert property (
        @(posedge clk) !shift_left |-> (out == (in >> shift_amt))
    );

// A zero shift amount passes the input through unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk) (shift_amt == 4'd0) |-> (out == in)
    );

// Left shift by 15 moves the input MSB into bit 0.
    check_left_shift_msb_into_lsb: assert property (
        @(posedge clk) (shift_left && (shift_amt == 4'd15)) |-> (out == {in[14:0], 1'b0})
    );

// Right shift by 15 moves the input LSB into bit 15.
    check_right_shift_lsb_into_msb: assert property (
        @(posedge clk) (!shift_left && (shift_amt == 4'd15)) |-> (out == {14'b0, in[0]})
    );

// Left shift by 16 clears the output to zero.
    check_left_shift_by_16_clears: assert property (
        @(posedge clk) (shift_left && (shift_amt == 4'd16)) |-> (out == 16'h0000)
    );

// Right shift by 16 clears the output to zero.
    check_right_shift_by_16_clears: assert property (
        @(posedge clk) (!shift_left && (shift_amt == 4'd16)) |-> (out == 16'h0000)
    );

endmodule

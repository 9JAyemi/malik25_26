module barrel_shifter_sva (
    input logic CLK,
    input logic [15:0] in,
    input logic [3:0] shift,
    input logic dir,
    input logic [15:0] out
);

// No reset in RTL; assertions are always active.

    // dir=0: out equals in shifted left by shift amount.
    check_left_shift_function: assert property (
        @(posedge CLK) (dir == 1'b0) |-> (out == (in << shift))
    );

// dir=1: out equals in shifted right by shift amount.
    check_right_shift_function: assert property (
        @(posedge CLK) (dir == 1'b1) |-> (out == (in >> shift))
    );

// Shift by 0 returns the input unchanged.
    check_shift_zero_passthrough: assert property (
        @(posedge CLK) (shift == 4'd0) |-> (out == in)
    );

// Left shift by 1: LSB becomes 0, upper bits shift up by 1.
    check_left_shift_by_one: assert property (
        @(posedge CLK) (dir == 1'b0 && shift == 4'd1) |-> (out == {in[14:0], 1'b0})
    );

// Right shift by 1: MSB becomes 0, lower bits shift down by 1.
    check_right_shift_by_one: assert property (
        @(posedge CLK) (dir == 1'b1 && shift == 4'd1) |-> (out == {1'b0, in[15:1]})
    );

// Left shift by 15: out equals MSB replicated 16 times.
    check_left_shift_by_fifteen: assert property (
        @(posedge CLK) (dir == 1'b0 && shift == 4'd15) |-> (out == {16{in[15]}})
    );

// Right shift by 15: out equals LSB replicated 16 times.
    check_right_shift_by_fifteen: assert property (
        @(posedge CLK) (dir == 1'b1 && shift == 4'd15) |-> (out == {16{in[0]}})
    );

// Left shift by 16: out equals zero.
    check_left_shift_by_sixteen: assert property (
        @(posedge CLK) (dir == 1'b0 && shift == 4'd16) |-> (out == 16'h0000)
    );

// Right shift by 16: out equals zero.
    check_right_shift_by_sixteen: assert property (
        @(posedge CLK) (dir == 1'b1 && shift == 4'd16) |-> (out == 16'h0000)
    );

endmodule

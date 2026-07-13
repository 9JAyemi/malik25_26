module barrel_shifter_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [3:0]  shift,
    input logic        dir,
    input logic [15:0] out
);

    // RTL is combinational, so assertions are sampled on an external clock.

    // Checks left mode performs two successive left shifts.
    check_left_direction_double_shift: assert property (
        @(posedge clk)
        (dir == 1'b0) |-> (out == ((in << shift) << shift))
    );

    // Checks right mode performs two successive right shifts.
    check_right_direction_double_shift: assert property (
        @(posedge clk)
        (dir == 1'b1) |-> (out == ((in >> shift) >> shift))
    );

    // Checks a zero shift passes the input through unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk)
        (shift == 4'd0) |-> (out == in)
    );

    // Checks shifts of 8 or more clear the 16-bit result after two stages.
    check_large_shift_clears_output: assert property (
        @(posedge clk)
        (shift >= 4'd8) |-> (out == 16'h0000)
    );

    // Checks left shifts insert zeros into the low bits.
    check_left_shift_zero_fills_low_bits: assert property (
        @(posedge clk)
        (dir == 1'b0 && shift != 4'd0) |-> (out[1:0] == 2'b00)
    );

    // Checks right shifts insert zeros into the high bits.
    check_right_shift_zero_fills_high_bits: assert property (
        @(posedge clk)
        (dir == 1'b1 && shift != 4'd0) |-> (out[15:14] == 2'b00)
    );

endmodule
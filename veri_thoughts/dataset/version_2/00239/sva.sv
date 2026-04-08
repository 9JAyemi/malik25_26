module bitwise_shift_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] y
);

    // y must always equal 12345 logically right-shifted by a.
    check_shift_result: assert property (
        @(posedge clk) y == (32'd12345 >> a)
    );

    // A zero shift must leave the constant unchanged.
    check_shift_by_zero: assert property (
        @(posedge clk) (a == 32'd0) |-> (y == 32'd12345)
    );

    // Shift amounts of 14 or more must produce zero.
    check_large_shift_zero: assert property (
        @(posedge clk) (a >= 32'd14) |-> (y == 32'd0)
    );

    // Right-shifting 12345 can never set bits above bit 13.
    check_upper_bits_zero: assert property (
        @(posedge clk) y[31:14] == 18'd0
    );

endmodule
module barrel_shifter_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [3:0]  shift_amt,
    input logic        shift_left,
    input logic [15:0] out
);

    // Left shift mode must produce the left-shifted value.
    check_left_shift_result: assert property (
        @(posedge clk) shift_left |-> (out == (in << shift_amt))
    );

    // Right shift mode must produce the right-shifted value.
    check_right_shift_result: assert property (
        @(posedge clk) !shift_left |-> (out == (in >> shift_amt))
    );

    // A zero shift amount must pass the input through unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk) (shift_amt == 4'd0) |-> (out == in)
    );

    // Left shift by 15 must leave only the original MSB.
    check_left_shift_max: assert property (
        @(posedge clk) (shift_left && (shift_amt == 4'd15)) |-> (out == {15'b0, in[15]})
    );

    // Right shift by 15 must leave only the original LSB.
    check_right_shift_max: assert property (
        @(posedge clk) (!shift_left && (shift_amt == 4'd15)) |-> (out == {in[0], 15'b0})
    );

    // Left shift by 1 must move the original MSB into bit 1.
    check_left_shift_by_one: assert property (
        @(posedge clk) (shift_left && (shift_amt == 4'd1)) |-> (out == {in[14:0], in[15]})
    );

    // Right shift by 1 must move the original LSB into bit 14.
    check_right_shift_by_one: assert property (
        @(posedge clk) (!shift_left && (shift_amt == 4'd1)) |-> (out == {in[0], in[15:1]})
    );

    // Left shift by 8 must move the original upper byte into the lower byte.
    check_left_shift_by_eight: assert property (
        @(posedge clk) (shift_left && (shift_amt == 4'd8)) |-> (out == {in[7:0], in[15:8]})
    );

    // Right shift by 8 must move the original lower byte into the upper byte.
    check_right_shift_by_eight: assert property (
        @(posedge clk) (!shift_left && (shift_amt == 4'd8)) |-> (out == {in[15:8], in[7:0]})
    );

endmodule
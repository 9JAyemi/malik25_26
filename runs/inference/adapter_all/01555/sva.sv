module barrel_shifter_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [3:0]  shift,
    input logic        dir,
    input logic [15:0] out
);

    // Output must match the selected shift operation.
    check_shift_function: assert property (
        @(posedge clk) out == (dir ? (in >> shift) : (in << shift))
    );

    // Zero shift must pass the input through unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk) (shift == 4'd0) |-> (out == in)
    );

    // Left shift by one must insert a zero into the least-significant bit.
    check_left_shift_by_one: assert property (
        @(posedge clk) (dir == 1'b0 && shift == 4'd1) |-> (out == {in[14:0], 1'b0})
    );

    // Right shift by one must insert a zero into the most-significant bit.
    check_right_shift_by_one: assert property (
        @(posedge clk) (dir == 1'b1 && shift == 4'd1) |-> (out == {1'b0, in[15:1]})
    );

    // Left shift by eight must zero the lower eight bits.
    check_left_shift_by_eight: assert property (
        @(posedge clk) (dir == 1'b0 && shift == 4'd8) |-> (out == {in[7:0], 8'h00})
    );

    // Right shift by eight must zero the upper eight bits.
    check_right_shift_by_eight: assert property (
        @(posedge clk) (dir == 1'b1 && shift == 4'd8) |-> (out == {8'h00, in[7:0]})
    );

    // Left shift by fifteen must move the input into the upper seven bits.
    check_left_shift_by_fifteen: assert property (
        @(posedge clk) (dir == 1'b0 && shift == 4'd15) |-> (out == {in[0], 7'h00})
    );

    // Right shift by fifteen must move the input into the lower seven bits.
    check_right_shift_by_fifteen: assert property (
        @(posedge clk) (dir == 1'b1 && shift == 4'd15) |-> (out == {7'h00, in[15]})
    );

endmodule
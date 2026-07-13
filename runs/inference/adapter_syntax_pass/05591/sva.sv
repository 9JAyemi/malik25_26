module barrel_shifter_sva (
    input logic [15:0] in,
    input logic [3:0]  shift,
    input logic        dir,
    input logic [15:0] out
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // out must match the RTL's nested shift expression.
    check_out_matches_rtl_expression: assert property (
        @($global_clock)
        out == ((dir == 1'b0) ? ((in << shift) << shift) : ((in >> shift) >> shift))
    );

    // A zero shift must pass the input through unchanged.
    check_zero_shift_passthrough: assert property (
        @($global_clock)
        (shift == 4'd0) |-> (out == in)
    );

    // A zero shift must also pass the input through when the direction is high.
    check_zero_shift_passthrough_dir_high: assert property (
        @($global_clock)
        ((shift == 4'd0) && (dir == 1'b1)) |-> (out == in)
    );

    // A zero shift must also pass the input through when the direction is low.
    check_zero_shift_passthrough_dir_low: assert property (
        @($global_clock)
        ((shift == 4'd0) && (dir == 1'b0)) |-> (out == in)
    );

    // A zero shift must also pass the input through when the direction is high.
    check_zero_shift_passthrough_dir_high: assert property (
        @($global_clock)
        ((shift == 4'd0) && (dir == 1'b1)) |-> (out == in)
    );

    // A zero shift must also pass the input through when the direction is low.
    check_zero_shift_passthrough_dir_low: assert property (
        @($global_clock)
        ((shift == 4'd0) && (dir == 1'b0)) |-> (out == in)
    );

    // A zero shift must also pass the input through when the direction is high.
    check_zero_shift_passthrough_dir_high: assert property (
        @($global_clock)
        ((shift == 4'd0) && (dir == 1'b1)) |-> (out == in)
    );

    // A zero shift must also pass the input through when the direction is low.
    check_zero_shift_passthrough_dir_low: assert property (
        @($global_clock)
        ((shift == 4'd0) && (dir == 1'b0)) |-> (out == in)
    );

    // A zero shift must also pass the input through when the direction is high.
    check_zero_shift_passthrough_dir_high: assert property (
        @($global_clock)
        ((shift == 4'd0) && (dir == 1'b1)) |-> (out == in)
    );

    // A zero shift must also pass the input through when the direction is low.
    check_zero_shift_passthrough_dir_low: assert property (
        @($global_clock)
        ((shift == 4'd0) && (dir == 1'b0)) |-> (out == in)
    );

endmodule
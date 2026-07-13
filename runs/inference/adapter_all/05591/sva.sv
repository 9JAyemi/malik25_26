module barrel_shifter_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [3:0]  shift,
    input logic        dir,
    input logic [15:0] out
);

    // RTL is combinational and has no reset; clk is a sampling clock.

    // Output matches the implemented two-stage barrel-shifter behavior.
    check_output_matches_two_stage_shift: assert property (
        @(posedge clk)
        out == ((dir == 1'b0) ? ((in << shift) << shift) : ((in >> shift) >> shift))
    );

    // A zero shift amount passes the input through unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk)
        (shift == 4'd0) |-> (out == in)
    );

    // A zero direction value uses left shift in both stages.
    check_left_direction_two_stage: assert property (
        @(posedge clk)
        (dir == 1'b0) |-> (out == ((in << shift) << shift))
    );

    // A one direction value uses right shift in both stages.
    check_right_direction_two_stage: assert property (
        @(posedge clk)
        (dir == 1'b1) |-> (out == ((in >> shift) >> shift))
    );

    // A zero direction value with a zero shift amount passes the input through unchanged.
    check_left_zero_shift_passthrough: assert property (
        @(posedge clk)
        (dir == 1'b0 && shift == 4'd0) |-> (out == in)
    );

    // A one direction value with a zero shift amount passes the input through unchanged.
    check_right_zero_shift_passthrough: assert property (
        @(posedge clk)
        (dir == 1'b1 && shift == 4'd0) |-> (out == in)
    );

    // A zero direction value with a nonzero shift amount doubles the left shift.
    check_left_nonzero_shift_doubles: assert property (
        @(posedge clk)
        (dir == 1'b0 && shift != 4'd0) |-> (out == (in << (shift + shift)))
    );

    // A one direction value with a nonzero shift amount doubles the right shift.
    check_right_nonzero_shift_doubles: assert property (
        @(posedge clk)
        (dir == 1'b1 && shift != 4'd0) |-> (out == (in >> (shift + shift)))
    );

endmodule
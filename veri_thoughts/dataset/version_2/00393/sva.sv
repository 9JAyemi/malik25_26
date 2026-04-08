module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [15:0] data_in,
    input logic [3:0]  shift_amt,
    input logic [3:0]  count_out,
    input logic [15:0] shifted_data
);

    // Reset drives the counter output to zero.
    check_reset_clears_counter: assert property (
        @(posedge clk) reset |=> (count_out == 4'h0)
    );

    // The counter increments by one when below 4'hF.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset)
        (count_out != 4'hF) |=> (count_out == ($past(count_out) + 4'h1))
    );

    // The counter wraps to zero after reaching 4'hF.
    check_counter_wraps: assert property (
        @(posedge clk) disable iff (reset)
        (count_out == 4'hF) |=> (count_out == 4'h0)
    );

    // The barrel shifter output matches a logical left shift.
    check_shift_matches_left_shift: assert property (
        @(posedge clk) disable iff (reset)
        (shifted_data == (data_in << shift_amt))
    );

    // A zero shift leaves the input unchanged.
    check_shift_zero_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (shift_amt == 4'h0) |-> (shifted_data == data_in)
    );

    // A shift by fifteen moves bit 0 into the MSB position.
    check_shift_fifteen_endpoint: assert property (
        @(posedge clk) disable iff (reset)
        (shift_amt == 4'hF) |-> (shifted_data == {data_in[0], 15'b0})
    );

    // Any nonzero left shift clears the output LSB.
    check_shift_nonzero_clears_lsb: assert property (
        @(posedge clk) disable iff (reset)
        (shift_amt != 4'h0) |-> (shifted_data[0] == 1'b0)
    );

endmodule
module top_module_sva (
    input logic clk,
    input logic rst_n,
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [7:0] data_in,
    input logic valid_a,
    input logic ready_b,
    input logic ready_a,
    input logic valid_b,
    input logic [9:0] data_out
);

    // ready_a is a direct pass-through of ready_b.
    check_ready_passthrough: assert property (
        @(posedge clk) disable iff (!rst_n)
        (ready_a == ready_b)
    );

    // valid_b is driven low while reset is asserted.
    check_valid_b_reset_low: assert property (
        @(posedge clk)
        (!rst_n) |-> (valid_b == 1'b0)
    );

    // valid_b goes high one cycle after valid_a is high.
    check_valid_b_sets_after_valid_a: assert property (
        @(posedge clk) disable iff (!rst_n)
        valid_a |=> (valid_b == 1'b1)
    );

    // valid_b goes low one cycle after valid_a is low.
    check_valid_b_clears_after_invalid_a: assert property (
        @(posedge clk) disable iff (!rst_n)
        (!valid_a) |=> (valid_b == 1'b0)
    );

    // data_out[3:1] reflects the bitwise OR of a and b.
    check_data_out_bitwise_or_bits: assert property (
        @(posedge clk) disable iff (!rst_n)
        (data_out[3:1] == (a | b))
    );

    // data_out[0] reflects the logical OR of nonzero a and b.
    check_data_out_logical_or_bit: assert property (
        @(posedge clk) disable iff (!rst_n)
        (data_out[0] == ((a != 3'b000) || (b != 3'b000)))
    );

    // The logical OR bit matches whether the bitwise OR bits are nonzero.
    check_logical_bit_matches_bitwise_nonzero: assert property (
        @(posedge clk) disable iff (!rst_n)
        (data_out[0] == (data_out[3:1] != 3'b000))
    );

    // data_out[9:4] resets to zero with the accumulator.
    check_accumulator_low_bits_reset_zero: assert property (
        @(posedge clk)
        (!rst_n) |-> (data_out[9:4] == 6'b0)
    );

    // data_out[9:4] holds when valid_a is low.
    check_accumulator_low_bits_hold_when_invalid: assert property (
        @(posedge clk) disable iff (!rst_n)
        (!valid_a) |=> (data_out[9:4] == $past(data_out[9:4]))
    );

    // data_out[9:4] adds data_in[5:0] when valid_a is high.
    check_accumulator_low_bits_add_when_valid: assert property (
        @(posedge clk) disable iff (!rst_n)
        valid_a |=> (data_out[9:4] == ($past(data_out[9:4]) + $past(data_in[5:0])))
    );

endmodule
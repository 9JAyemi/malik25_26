module parity_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [7:0] in,
    input logic [7:0] out
);

    // Clock: clk. Reset: reset, asynchronous active-high.
    // Mixed logic: sequential counter with combinational parity and output mapping.

    // During reset, the counter nibble is held at zero.
    check_reset_count_zero: assert property (
        @(posedge clk) reset |-> (out[3:0] == 4'h0)
    );

    // During reset, the difference nibble is 0 minus the input parity.
    check_reset_diff_matches_parity: assert property (
        @(posedge clk) reset |-> (out[7:4] == ((^in) ? 4'hF : 4'h0))
    );

    // After any sampled reset cycle, the next sampled counter nibble is still zero.
    check_post_reset_count_zero: assert property (
        @(posedge clk) reset |=> (out[3:0] == 4'h0)
    );

    // After any sampled reset cycle, the next sampled difference nibble still reflects zero count.
    check_post_reset_diff_matches_parity: assert property (
        @(posedge clk) reset |=> (out[7:4] == ((^in) ? 4'hF : 4'h0))
    );

    // Across non-reset cycles, the counter nibble increments by one modulo 16.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (out[3:0] == ($past(out[3:0]) + 4'h1))
    );

    // With even input parity, the difference nibble matches the counter nibble.
    check_even_parity_diff: assert property (
        @(posedge clk) disable iff (reset) ((^in) == 1'b0) |-> (out[7:4] == out[3:0])
    );

    // With odd input parity, the difference nibble is one less than the counter nibble.
    check_odd_parity_diff: assert property (
        @(posedge clk) disable iff (reset) ((^in) == 1'b1) |-> (out[7:4] == (out[3:0] - 4'h1))
    );

endmodule
module concat_8bit_sva (
    input logic        clk,
    input logic        reset,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic        ctrl,
    input logic [15:0] out
);

    // A sampled reset must leave the registered output cleared on the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (out == 16'b0)
    );

    // The first clock after reset deassertion still sees the cleared register value.
    check_reset_release_keeps_zero_until_update: assert property (
        @(posedge clk) $fell(reset) |-> (out == 16'b0)
    );

    // When ctrl is high, the next registered output is {a, b}.
    check_ctrl_high_concatenates_a_then_b: assert property (
        @(posedge clk) disable iff (reset)
        ctrl |=> (out == {$past(a), $past(b)})
    );

    // When ctrl is low, the next registered output is {b, a}.
    check_ctrl_low_concatenates_b_then_a: assert property (
        @(posedge clk) disable iff (reset)
        !ctrl |=> (out == {$past(b), $past(a)})
    );

endmodule
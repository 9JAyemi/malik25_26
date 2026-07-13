module async_reset_release_sva (
    input logic reset,
    input logic clk,
    input logic in,
    input logic out
);

    // Output is still low on the first clock after reset is released.
    check_output_low_on_reset_release: assert property (
        @(posedge clk) disable iff (!reset)
        (!$initstate && $rose(reset)) |-> (out == 1'b0)
    );

    // A low input on an active clock produces a low output on the next clock.
    check_low_input_captures_low: assert property (
        @(posedge clk) disable iff (!reset)
        (!in) |=> (out == 1'b0)
    );

    // A high output must come from a previous active clock with high input.
    check_high_output_requires_prev_high_input: assert property (
        @(posedge clk) disable iff (!reset)
        (!$initstate && out) |-> ($past(reset) && $past(in))
    );

endmodule
module d_flip_flop_async_reset_enable_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic data,
    input logic out
);

    // Synchronous reset clears out.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 1'b0)
    );

    // When enabled and not in reset, out captures data.
    check_enable_captures_data: assert property (
        @(posedge clk) disable iff (reset) enable |=> (out == $past(data))
    );

    // When not enabled and not in reset, out holds its value.
    check_disable_holds_out: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (out == $past(out))
    );

endmodule
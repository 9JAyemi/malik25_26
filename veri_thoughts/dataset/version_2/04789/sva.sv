module d_ff_async_reset_enable_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic data_in,
    input logic data_out
);

    // Reset drives the flop output low.
    check_reset_clears_output: assert property (
        @(posedge clk) !reset |-> (data_out == 1'b0)
    );

    // With enable high and data_in high, the output becomes high on the next cycle.
    check_enable_captures_one: assert property (
        @(posedge clk) disable iff (!reset)
        (enable && data_in) |=> (data_out == 1'b1)
    );

    // With enable high and data_in low, the output becomes low on the next cycle.
    check_enable_captures_zero: assert property (
        @(posedge clk) disable iff (!reset)
        (enable && !data_in) |=> (data_out == 1'b0)
    );

    // With enable low, the output holds its value.
    check_disable_holds_output: assert property (
        @(posedge clk) disable iff (!reset)
        (!enable) |=> $stable(data_out)
    );

endmodule
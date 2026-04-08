module counter_sva(
    input logic       clk,
    input logic       reset,
    input logic       up_down,
    input logic [3:0] out
);

    // Reset clears the counter on the next sampled clock.
    reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 4'b0000)
    );

    // With reset low and up_down high, the counter increments by one.
    count_up_step: assert property (
        @(posedge clk) disable iff (reset)
        up_down |=> (out == ($past(out) + 4'd1))
    );

    // With reset low and up_down low, the counter decrements by one.
    count_down_step: assert property (
        @(posedge clk) disable iff (reset)
        !up_down |=> (out == ($past(out) - 4'd1))
    );

    // Counting up from 4'hF wraps around to 4'h0.
    up_wraps_from_f_to_0: assert property (
        @(posedge clk) disable iff (reset)
        up_down && (out == 4'hF) |=> (out == 4'h0)
    );

    // Counting down from 4'h0 wraps around to 4'hF.
    down_wraps_from_0_to_f: assert property (
        @(posedge clk) disable iff (reset)
        !up_down && (out == 4'h0) |=> (out == 4'hF)
    );

endmodule
module counter_assertions (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // A reset clock edge clears the counter by the next sampled cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // On consecutive non-reset cycles, the counter increments by one.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset)
        (!reset ##1 !reset) |-> (count == ($past(count) + 4'd1))
    );

    // A max count value wraps to zero on the next non-reset cycle.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset)
        ((count == 4'hF) ##1 !reset) |-> (count == 4'h0)
    );

endmodule
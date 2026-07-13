module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] out
);

    // A reset cycle clears all four sub-counters, so the next sampled output is zero.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 8'h00)
    );

    // On reset release, the sampled output still reflects count value 0 in all slices.
    check_release_starts_at_zero: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (out == 8'h00)
    );

    // One cycle after reset release, all four slices advance to 2'b01.
    check_release_step_01: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> (out == 8'h55)
    );

    // Two cycles after reset release, all four slices advance to the first 2'b10 state.
    check_release_step_10_first: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##1 (out == 8'hAA)
    );

    // Three cycles after reset release, all four slices remain at 2'b10.
    check_release_step_10_second: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##2 (out == 8'hAA)
    );

    // Four cycles after reset release, all four slices advance to the first 2'b11 state.
    check_release_step_11_first: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##3 (out == 8'hFF)
    );

    // Five cycles after reset release, all four slices remain at 2'b11.
    check_release_step_11_second: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##4 (out == 8'hFF)
    );

    // Six cycles after reset release, all four slices still remain at 2'b11.
    check_release_step_11_third: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##5 (out == 8'hFF)
    );

    // Seven cycles after reset release, the counters wrap and the output returns to zero.
    check_release_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##6 (out == 8'h00)
    );

endmodule
module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic [7:0] q,
    input logic [7:0] count
);

    // Reset clears the register output on the next clock.
    check_reg_reset_clears_q: assert property (
        @(posedge clk) reset |=> (q == 8'h00)
    );

    // Reset clears the counter output on the next clock.
    check_counter_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 8'h00)
    );

    // The register captures the sum of d1 and d2 when enabled.
    check_reg_captures_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (q == ($past(d1) + $past(d2)))
    );

    // The counter increments by one when enabled.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (count == ($past(count) + 8'd1))
    );

endmodule
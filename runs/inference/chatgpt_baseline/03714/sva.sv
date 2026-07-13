module dffl_64_sva (
    input logic        clk,
    input logic        ld,
    input logic        rst,
    input logic [63:0] d,
    input logic [63:0] q
);

    // Synchronous reset clears q to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) rst |=> (q == 64'b0)
    );

    // Reset overrides load when both are asserted.
    check_reset_priority_over_load: assert property (
        @(posedge clk) (rst && ld) |=> (q == 64'b0)
    );

    // Load causes q to capture d on the next sampled cycle.
    check_load_captures_d: assert property (
        @(posedge clk) disable iff (rst) ld |=> (q == $past(d))
    );

    // Without load, q holds its previous value.
    check_hold_when_load_low: assert property (
        @(posedge clk) disable iff (rst) !ld |=> (q == $past(q))
    );

endmodule